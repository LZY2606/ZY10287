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

package engine

import (
	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/unionfind"
)

// PremiseRef describes one position of a rule body and the concrete value
// that satisfied it for a particular rule firing.
type PremiseRef struct {
	// Index is the position of this premise in the (normalized) rule body.
	Index int
	// Kind classifies the premise.
	Kind PremiseKind
	// Atom is the ground atom that matched a positive atom premise or a
	// temporal-literal premise. It is the zero value for Eq/Ineq premises.
	Atom ast.Atom
	// Interval is the validity interval of the matching temporal fact;
	// nil for premises that are not temporal.
	Interval *ast.Interval
	// Literal is the source text of a built-in (Eq/Ineq) premise, e.g.
	// "X != Y".
	Literal string
	// Predicate is the relation checked by a negated premise, after
	// substitution. It is the pattern the engine looked for; it must not
	// be mistaken for a fact that exists in the store.
	Predicate ast.Atom
	// Temporal is true if this premise was written as a temporal literal.
	Temporal bool
}

// PremiseKind classifies a recorded premise.
type PremiseKind int

const (
	// PremiseAtom is a positive subgoal atom.
	PremiseAtom PremiseKind = iota
	// PremiseBuiltin is an Eq/Ineq (or built-in predicate) check.
	PremiseBuiltin
	// PremiseNegation is a negated atom premise that succeeded by absence.
	PremiseNegation
	// PremiseTemporal is a positive temporal-literal subgoal.
	PremiseTemporal
)

// RuleFiring captures one application of a plain Datalog rule.
type RuleFiring struct {
	// Rule is the originating clause, with delta-prefixed predicates
	// normalized back to their source form.
	Rule ast.Clause
	// Head is the ground derived atom.
	Head ast.Atom
	// HeadInterval is the validity interval of a temporally-annotated
	// head; nil for non-temporal rules.
	HeadInterval *ast.Interval
	// Subst is the substitution that satisfied the body.
	Subst unionfind.UnionFind
	// Stratum is the stratification index in which the rule fired.
	Stratum int
	// Iteration is the fixed-point iteration within the stratum: 0 for
	// the initial round, 1..n for semi-naive incremental rounds.
	Iteration int
	// Premises describes every body position, in body order.
	Premises []PremiseRef
}

// LetEmission captures one output row of a let-transform.
type LetEmission struct {
	Rule          ast.Clause
	Head          ast.Atom
	HeadInterval  *ast.Interval
	Row           ast.ConstSubstList
	Output        ast.Atom
	Stratum       int
	Iteration     int
	TransformText string
}

// DoEmission captures one output row of a do-transform (one per group).
type DoEmission struct {
	Rule          ast.Clause
	Head          ast.Atom
	GroupKey      []ast.Constant
	// InputFacts lists, in arrival order, one fact per row that fed the
	// group. Duplicates are retained: this is a multiset.
	InputFacts    []ast.Atom
	Output        ast.Atom
	Stratum       int
	TransformText string
}

// DerivationRecorder receives a callback every time a rule produces an
// output fact. Implementations are responsible for buffering/persisting
// events; the engine does not retain them after the callback returns.
//
// The recorder is an optional evaluation hook used by the provenance
// package to capture "full" provenance during computation. When no
// recorder is configured, none of the callbacks fire — there is no
// overhead in the hot path beyond a nil check per derivation.
type DerivationRecorder interface {
	// RuleFired is invoked for each solution of a plain Datalog rule
	// (including rules whose only transform is a let-transform; see
	// LetEmit for the corresponding post-transform output).
	RuleFired(firing RuleFiring)

	// LetEmit is invoked once per output of a let-transform, i.e. once
	// per input solution row.
	LetEmit(emission LetEmission)

	// DoEmit is invoked once per output of a do-transform (one per
	// group). The emission carries the group key and the input multiset.
	DoEmit(emission DoEmission)
}

// WithDerivationRecorder installs a DerivationRecorder. Pass nil to
// disable (the default). When set, the engine calls the recorder's
// methods at each derivation point; when unset, the callbacks are
// skipped with a single nil check.
func WithDerivationRecorder(r DerivationRecorder) EvalOption {
	return func(o *EvalOptions) { o.recorder = r }
}
