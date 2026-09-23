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
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/unionfind"
)

// Event is one recorded derivation. A given output fact may have multiple
// events (alternative derivations).
type Event struct {
	Kind          EventKind
	Rule          ast.Clause
	Head          ast.Atom
	HeadInterval  *ast.Interval
	Subst         unionfind.UnionFind // set for EventRule only
	Row           ast.ConstSubstList  // set for EventLet only
	PremiseRefs   []engine.PremiseRef // set for EventRule; one entry per body position
	GroupKey      []ast.Constant      // set for EventDo only
	InputFacts    []ast.Atom          // set for EventDo only; multiset, duplicates retained
	Output        ast.Atom            // always set
	TransformText string              // set for EventLet and EventDo
	Stratum       int
	Iteration     int
}

// EventKind tags the type of a recorded derivation.
type EventKind int

const (
	// EventRule is a plain Datalog rule firing (no transform).
	EventRule EventKind = iota
	// EventLet is a let-transform output (one per input row).
	EventLet
	// EventDo is a do-transform output (one per group).
	EventDo
)

// MemoryRecorder implements [engine.DerivationRecorder] by buffering every
// event in memory. After evaluation, pass the recorder to
// [BuildFromRecording] or [BuildProofGraph] to inspect provenance.
//
// MemoryRecorder is not safe for concurrent use; the engine does not run
// eval in parallel, so this is fine in practice.
type MemoryRecorder struct {
	// byOutputHash maps an output atom's hash to all events concluding it.
	// Multiple entries mean the same fact was derived in more than one
	// way during evaluation.
	byOutputHash map[uint64][]*Event
	all          []*Event
	// firing is a monotonic counter used only to break ties between
	// events recorded during the same stratum/iteration.
	firing int64
}

// Ensure MemoryRecorder satisfies the engine interface.
var _ engine.DerivationRecorder = (*MemoryRecorder)(nil)

// NewMemoryRecorder returns a fresh, empty recorder.
func NewMemoryRecorder() *MemoryRecorder {
	return &MemoryRecorder{byOutputHash: make(map[uint64][]*Event)}
}

// RuleFired implements engine.DerivationRecorder.
func (r *MemoryRecorder) RuleFired(firing engine.RuleFiring) {
	r.firing++
	ev := &Event{
		Kind:         EventRule,
		Rule:         firing.Rule,
		Head:         firing.Head,
		HeadInterval: firing.HeadInterval,
		Subst:        firing.Subst,
		PremiseRefs:  append([]engine.PremiseRef(nil), firing.Premises...),
		Output:       firing.Head,
		Stratum:      firing.Stratum,
		Iteration:    firing.Iteration,
	}
	r.add(ev)
}

// LetEmit implements engine.DerivationRecorder.
func (r *MemoryRecorder) LetEmit(emission engine.LetEmission) {
	r.firing++
	ev := &Event{
		Kind:          EventLet,
		Rule:          emission.Rule,
		Head:          emission.Head,
		HeadInterval:  emission.HeadInterval,
		Row:           emission.Row,
		Output:        emission.Output,
		TransformText: emission.TransformText,
		Stratum:       emission.Stratum,
		Iteration:     emission.Iteration,
	}
	r.add(ev)
}

// DoEmit implements engine.DerivationRecorder.
func (r *MemoryRecorder) DoEmit(emission engine.DoEmission) {
	r.firing++
	ev := &Event{
		Kind:          EventDo,
		Rule:          emission.Rule,
		Head:          emission.Head,
		GroupKey:      append([]ast.Constant(nil), emission.GroupKey...),
		InputFacts:    append([]ast.Atom(nil), emission.InputFacts...),
		Output:        emission.Output,
		TransformText: emission.TransformText,
		Stratum:       emission.Stratum,
	}
	r.add(ev)
}

func (r *MemoryRecorder) add(ev *Event) {
	r.all = append(r.all, ev)
	h := ev.Output.Hash()
	r.byOutputHash[h] = append(r.byOutputHash[h], ev)
}

// Events returns all recorded events in order of arrival.
func (r *MemoryRecorder) Events() []*Event { return r.all }

// EventsFor returns all events whose output equals the given atom.
// Multiple entries mean alternative derivations of the same fact.
func (r *MemoryRecorder) EventsFor(a ast.Atom) []*Event {
	var out []*Event
	for _, ev := range r.byOutputHash[a.Hash()] {
		if ev.Output.Equals(a) {
			out = append(out, ev)
		}
	}
	return out
}

// sortEvents returns a copy of events in a canonical order that does not
// depend on Go map iteration inside the engine: first by stratum, then by
// fixed-point iteration, then by rule text, then by the derived atom.
func sortEvents(events []*Event) []*Event {
	out := append([]*Event(nil), events...)
	sort.SliceStable(out, func(i, j int) bool {
		a, b := out[i], out[j]
		if a.Stratum != b.Stratum {
			return a.Stratum < b.Stratum
		}
		if a.Iteration != b.Iteration {
			return a.Iteration < b.Iteration
		}
		if ra, rb := a.Rule.String(), b.Rule.String(); ra != rb {
			return ra < rb
		}
		return a.Output.String() < b.Output.String()
	})
	return out
}
