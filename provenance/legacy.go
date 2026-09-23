// Copyright 2026 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package provenance

import (
	"sort"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/factstore"
)

// BuildFromRecording assembles proof trees for the given goal from a
// recording. It uses the store to distinguish EDB leaves from derived
// facts, and to satisfy negated premises via closed-world absence.
// Options are the same as for [Explain].
//
// This is the flat, tree-shaped view (one premise edge per body atom,
// built-in checks omitted). For the richer, queryable graph with explicit
// subgoal/builtin/negation/temporal nodes and multiset edges use
// [BuildProofGraph].
func BuildFromRecording(rec *MemoryRecorder, store factstore.ReadOnlyFactStore, goal ast.Atom, opts Options) ([]*ProofNode, error) {
	if opts.MaxProofs == 0 {
		opts.MaxProofs = defaultMaxProofs
	}
	if opts.MaxDepth == 0 {
		opts.MaxDepth = defaultMaxDepth
	}
	if !isGround(goal) {
		return nil, ErrGoalNotGround
	}
	b := &legacyBuilder{
		rec:     rec,
		store:   store,
		opts:    opts,
		cache:   make(map[uint64][]*ProofNode),
		onStack: make(map[uint64]bool),
		ruleIDs: make(map[string]string),
	}
	proofs := b.build(goal, 0)
	if len(proofs) == 0 {
		return nil, ErrNoProof
	}
	return proofs, nil
}

type legacyBuilder struct {
	rec     *MemoryRecorder
	store   factstore.ReadOnlyFactStore
	opts    Options
	cache   map[uint64][]*ProofNode
	onStack map[uint64]bool
	ruleIDs map[string]string // rule.String() -> rule content ID
}

func (b *legacyBuilder) build(goal ast.Atom, depth int) []*ProofNode {
	if depth > b.opts.MaxDepth {
		return []*ProofNode{{Fact: goal, Partial: true, ID: partialID(goal)}}
	}
	h := goal.Hash()
	if cached, ok := b.cache[h]; ok {
		return cached
	}
	if b.onStack[h] {
		return nil
	}
	b.onStack[h] = true
	defer delete(b.onStack, h)

	var proofs []*ProofNode
	events := b.rec.EventsFor(goal)
	if len(events) == 0 {
		if b.store.Contains(goal) {
			proofs = append(proofs, &ProofNode{ID: edbProofID(goal), Fact: goal, Kind: KindEDB})
		}
		b.cache[h] = proofs
		return proofs
	}
	for _, ev := range sortEvents(events) {
		if len(proofs) >= b.opts.MaxProofs {
			break
		}
		p := b.buildFromEvent(ev, depth)
		if p == nil {
			continue
		}
		proofs = append(proofs, p)
	}
	b.cache[h] = proofs
	return proofs
}

func (b *legacyBuilder) ruleID(r ast.Clause) string {
	key := r.String()
	if id, ok := b.ruleIDs[key]; ok {
		return id
	}
	id := ruleContentID(r)
	b.ruleIDs[key] = id
	return id
}

func (b *legacyBuilder) buildFromEvent(ev *Event, depth int) *ProofNode {
	ruleID := b.ruleID(ev.Rule)
	switch ev.Kind {
	case EventRule:
		return b.buildRule(ev, ruleID, depth)
	case EventLet:
		return b.buildLet(ev, ruleID, depth)
	case EventDo:
		return b.buildDo(ev, ruleID, depth)
	}
	return nil
}

// premiseAtomFacts returns the matched atom for each body position; zero
// atoms mark non-atom or unmatched positions, as the original recorder
// contract promised.
func premiseAtomFacts(ev *Event) []ast.Atom {
	out := make([]ast.Atom, len(ev.PremiseRefs))
	for i, ref := range ev.PremiseRefs {
		out[i] = ref.Atom
	}
	return out
}

func (b *legacyBuilder) buildRule(ev *Event, ruleID string, depth int) *ProofNode {
	premiseFacts := premiseAtomFacts(ev)
	var premiseProofs []*ProofNode
	partial := false
	for i, p := range ev.Rule.Premises {
		switch term := p.(type) {
		case ast.Atom:
			if term.Predicate.IsBuiltin() {
				continue
			}
			fact := premiseFacts[i]
			if fact.Predicate.Symbol == "" {
				partial = true
				continue
			}
			sub := b.build(fact, depth+1)
			if len(sub) == 0 {
				partial = true
				continue
			}
			premiseProofs = append(premiseProofs, sub[0])
		case ast.NegAtom:
			if term.Atom.Predicate.IsBuiltin() {
				continue
			}
			ground, err := applyToNeg(term, ev.Subst)
			if err != nil || !isGround(ground) {
				partial = true
				continue
			}
			if b.store.Contains(ground) {
				partial = true
				continue
			}
			premiseProofs = append(premiseProofs, &ProofNode{
				ID:              absenceProofID(ground),
				Fact:            ground,
				Kind:            KindAbsence,
				CheckedRelation: ground,
			})
		case ast.Eq, ast.Ineq:
			// Satisfied by construction (the rule fired). No sub-proof.
		default:
			partial = true
		}
	}
	node := &ProofNode{
		Fact:      ev.Output,
		Kind:      KindDerived,
		Rule:      &ev.Rule,
		RuleID:    ruleID,
		Bindings:  extractBindings(ev.Rule, ev.Subst),
		Premises:  premiseProofs,
		Partial:   partial,
		Stratum:   ev.Stratum,
		Iteration: ev.Iteration,
		Interval:  ev.HeadInterval,
	}
	node.ID = derivedProofID(ruleID, ev.Output, premiseProofs)
	return node
}

func (b *legacyBuilder) buildLet(ev *Event, ruleID string, depth int) *ProofNode {
	var premiseProofs []*ProofNode
	partial := false
	for _, p := range ev.Rule.Premises {
		atom, ok := p.(ast.Atom)
		if !ok {
			continue
		}
		ground := atom.ApplySubst(ev.Row).(ast.Atom)
		if !isGround(ground) {
			partial = true
			continue
		}
		sub := b.build(ground, depth+1)
		if len(sub) == 0 {
			if b.store.Contains(ground) {
				sub = []*ProofNode{{ID: edbProofID(ground), Fact: ground, Kind: KindEDB}}
			} else {
				partial = true
				continue
			}
		}
		premiseProofs = append(premiseProofs, sub[0])
	}
	node := &ProofNode{
		Fact:          ev.Output,
		Kind:          KindLetRow,
		Rule:          &ev.Rule,
		RuleID:        ruleID,
		Premises:      premiseProofs,
		TransformText: ev.TransformText,
		Partial:       partial,
		Interval:      ev.HeadInterval,
	}
	node.ID = derivedProofID(ruleID, ev.Output, premiseProofs)
	return node
}

func (b *legacyBuilder) buildDo(ev *Event, ruleID string, depth int) *ProofNode {
	var premiseProofs []*ProofNode
	partial := false
	for _, f := range ev.InputFacts {
		sub := b.build(f, depth+1)
		if len(sub) == 0 {
			if b.store.Contains(f) {
				sub = []*ProofNode{{ID: edbProofID(f), Fact: f, Kind: KindEDB}}
			} else {
				partial = true
				continue
			}
		}
		premiseProofs = append(premiseProofs, sub[0])
	}
	// Deterministic premise order (groups arrive in nondeterministic map order
	// inside evalDo; the *set* of input facts is the same, but the order
	// varies run to run). Sort by proof ID for stable output.
	sort.Slice(premiseProofs, func(i, j int) bool {
		return premiseProofs[i].ID < premiseProofs[j].ID
	})
	node := &ProofNode{
		Fact:          ev.Output,
		Kind:          KindDoAggregate,
		Rule:          &ev.Rule,
		RuleID:        ruleID,
		GroupKey:      ev.GroupKey,
		Premises:      premiseProofs,
		TransformText: ev.TransformText,
		Partial:       partial,
	}
	node.ID = derivedProofID(ruleID, ev.Output, premiseProofs)
	return node
}

// applyToNeg applies a substitution (the rule's solution) to a negated atom.
func applyToNeg(n ast.NegAtom, subst ast.Subst) (ast.Atom, error) {
	if subst == nil {
		return n.Atom, nil
	}
	applied := n.Atom.ApplySubst(subst).(ast.Atom)
	return applied, nil
}
