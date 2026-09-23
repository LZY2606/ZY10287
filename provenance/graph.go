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
	"errors"
	"fmt"
	"sort"

	"codeberg.org/TauCeti/mangle-go/ast"
	"codeberg.org/TauCeti/mangle-go/engine"
	"codeberg.org/TauCeti/mangle-go/factstore"
)

// ProofGraph is a queryable provenance graph built from a derivation
// recording.
//
// Nodes are stable, content-addressed rule *occurrences*, subgoals,
// built-in checks, negation/absence leaves, temporal subgoals, aggregate
// groups and EDB base facts. Edges connect an occurrence to the concrete
// premise nodes that satisfied its body; shared sub-derivations point at
// the same node id, while every rule occurrence keeps its own variable
// bindings.
//
// Recursive SCCs are never unrolled indefinitely: an edge that closes a
// cycle is marked as a back-edge ([Edge.Back]) together with the
// fixed-point iteration at which the child occurrence fired.
type ProofGraph struct {
	// nodes maps stable node id to node, including every recorded
		// occurrence and reachable leaf.
	nodes map[string]*ProofNode
	// roots maps the string form of a derived atom to the ids of the
	// occurrence nodes that conclude it.
	roots map[string][]string
	// factIndex maps an atom string to the id of the node proving it.
	factIndex map[string]string
	// store is used for EDB/absence leaves and independent replay.
	store factstore.ReadOnlyFactStore
	// temporalStore is optional; it supplies validity intervals of base
	// temporal facts and supports temporal goals.
	temporalStore factstore.ReadOnlyTemporalFactStore
}

// GraphOptions tunes [BuildProofGraph].
type GraphOptions struct {
	// TemporalStore is an optional temporal store used to find base
	// temporal facts and their intervals.
	TemporalStore factstore.ReadOnlyTemporalFactStore
}

// ErrNodeNotFound is returned when a node id is not in the graph.
var ErrNodeNotFound = errors.New("provenance: proof node not found")

// BuildProofGraph builds the full proof graph from a recording. The simple
// store is used to identify EDB leaves and absence snapshots; pass a
// temporal store via GraphOptions for temporally annotated programs.
func BuildProofGraph(rec *MemoryRecorder, store factstore.ReadOnlyFactStore, opts GraphOptions) *ProofGraph {
	g := &ProofGraph{
		nodes:         make(map[string]*ProofNode),
		roots:         make(map[string][]string),
		factIndex:     make(map[string]string),
		store:         store,
		temporalStore: opts.TemporalStore,
	}
	for _, ev := range rec.Events() {
		node := g.nodeForEvent(ev)
		key := ev.Output.String()
		g.roots[key] = append(g.roots[key], node.ID)
		if _, ok := g.factIndex[key]; !ok {
			g.factIndex[key] = node.ID
		}
	}
	for _, ids := range g.roots {
		sort.Slice(ids, func(i, j int) bool { return ids[i] < ids[j] })
	}
	return g
}

// Node returns the node with the given id.
func (g *ProofGraph) Node(id string) (*ProofNode, error) {
	n, ok := g.nodes[id]
	if !ok {
		return nil, fmt.Errorf("%w: %s", ErrNodeNotFound, id)
	}
	return n, nil
}

// NodesForFact returns every occurrence node that concludes the given atom.
func (g *ProofGraph) NodesForFact(goal ast.Atom) []*ProofNode {
	var out []*ProofNode
	for _, id := range g.roots[goal.String()] {
		if n, ok := g.nodes[id]; ok {
			out = append(out, n)
		}
	}
	return out
}

// NodeForFact returns one node proving the given atom, preferring an
// occurrence node and falling back to an EDB/temporal leaf.
func (g *ProofGraph) NodeForFact(goal ast.Atom) (*ProofNode, error) {
	if id, ok := g.factIndex[goal.String()]; ok {
		return g.nodes[id], nil
	}
	if g.store != nil && g.store.Contains(goal) {
		return g.edbNode(goal, nil), nil
	}
	if g.temporalStore != nil {
		if n := g.temporalLeaf(goal); n != nil {
			return n, nil
		}
	}
	return nil, fmt.Errorf("%w: no node proves %s", ErrNodeNotFound, goal.String())
}

// Facts returns the atoms that have at least one proving node, sorted
// lexicographically for deterministic iteration.
func (g *ProofGraph) Facts() []string {
	out := make([]string, 0, len(g.factIndex))
	for k := range g.factIndex {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// MinimalProofs returns up to maxProofs minimal proofs of goal, ordered by
// number of edges (fewest first); ties are broken by the lexicographic
// sequence of node ids, so output is stable across runs and independent of
// input ordering. A proof is a tree view of the graph: each occurrence's
// own variable bindings are preserved; recursive cycles terminate at
// back-edges ([Edge.Back] == true).
func (g *ProofGraph) MinimalProofs(goal ast.Atom, maxProofs int) ([]*ProofNode, error) {
	if maxProofs <= 0 {
		maxProofs = defaultMaxProofs
	}
	if !isGround(goal) {
		return nil, ErrGoalNotGround
	}
	roots := g.NodesForFact(goal)
	if len(roots) == 0 {
		if g.store != nil && g.store.Contains(goal) {
			return []*ProofNode{g.edbNode(goal, nil)}, nil
		}
		if g.temporalStore != nil {
			if n := g.temporalLeaf(goal); n != nil {
				return []*ProofNode{n}, nil
			}
		}
		return nil, ErrNoProof
	}
	type cand struct {
		root *ProofNode
		cost int
		key  []string
	}
	var cands []cand
	for _, r := range roots {
		view, cost, key := g.viewOf(r, nil)
		cands = append(cands, cand{view, cost, key})
	}
	sortCandidates(cands)
	if len(cands) > maxProofs {
		cands = cands[:maxProofs]
	}
	out := make([]*ProofNode, len(cands))
	for i, c := range cands {
		out[i] = c.root
	}
	return out, nil
}

func sortCandidates(cands []struct {
	root *ProofNode
	cost int
	key  []string
}) {
	sort.SliceStable(cands, func(i, j int) bool {
		if cands[i].cost != cands[j].cost {
			return cands[i].cost < cands[j].cost
		}
		return lexLess(cands[i].key, cands[j].key)
	})
}

func lexLess(a, b []string) bool {
	for i := 0; i < len(a) && i < len(b); i++ {
		if a[i] != b[i] {
			return a[i] < b[i]
		}
	}
	return len(a) < len(b)
}

// viewOf materializes a tree rooted at id, reusing already-visited nodes
// via the onPath set. Cyclic edges become BackEdge leaves carrying the id
// of the ancestor they point to. It returns the view root, the edge count,
// and a pre-order list of node ids used for tie-breaking.
func (g *ProofGraph) viewOf(root *ProofNode, onPath map[string]bool) (*ProofNode, int, []string) {
	view := *root // shallow copy: occurrences keep their own bindings/edges
	view.Premises = nil
	view.Inputs = nil
	edges := 0
	var key []string

	visit := func(e Edge, backTo string) Edge {
		if backTo != "" {
			ref := *e.To
			ref.Premises = nil
			ref.Inputs = nil
			ref.BackEdge = true
			ref.BackRef = backTo
			edges++
			key = append(key, e.To.ID)
			return Edge{Index: e.Index, To: &ref, Multiplicity: e.Multiplicity, Iteration: e.Iteration}
		}
		child, childEdges, childKey := g.viewOf(e.To, onPath)
		edges += 1 + childEdges
		key = append(key, childKey...)
		return Edge{Index: e.Index, To: child, Multiplicity: e.Multiplicity, Iteration: e.Iteration}
	}

	for _, e := range root.childEdges() {
		var back string
		if onPath[e.To.ID] {
			back = e.To.ID
		}
		ne := visit(e, back)
		if back == "" {
			// only descend into non-back edges
		}
		_ = ne
	}
	// Rebuild with recursion using a path-aware walk (the closure above
	// needs the child's own path, so do it directly below).
	return g.buildView(root, nil)
}
