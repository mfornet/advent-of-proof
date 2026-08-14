import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Problem12

structure DisjointPair (A : Type) : Type where
  fromV : A
  toV  : A
  diff : toV ≠ fromV

structure MultiGraph : Type where
  numV : Nat
  E : List (DisjointPair (Fin numV))

variable (g : MultiGraph)

def MultiGraph.Vertex : Type := Fin (g.numV)
instance : DecidableEq (MultiGraph.Vertex g) := inferInstanceAs (DecidableEq (Fin g.numV))
def MultiGraph.Edge   : Type := DisjointPair (g.Vertex)

def MultiGraph.V : List (g.Vertex) := List.finRange g.numV
def MultiGraph.connects (v : g.Vertex)(e : g.Edge) : Bool := Decidable.decide (e.fromV = v) ∨ Decidable.decide (e.toV = v)
def MultiGraph.degree' (E : List (g.Edge)) (v : g.Vertex) : Nat := List.length (List.filter (g.connects v) E)
def MultiGraph.degree (v : g.Vertex) : Nat := g.degree' g.E v

-- An edge with a direction, true means it goes in the direction [fromV -> toV] and false otherwise.
abbrev directedEdge := DisjointPair (g.Vertex) × Bool

-- set_option trace.Meta.synthInstance true
-- All edges that are directed out of a vertex v
def outEdges (v : g.Vertex) : Set (directedEdge g) :=
  { x | x.1 ∈ g.E ∧ (x.2 = true → x.1.fromV = v) ∧ (x.2 = false → x.1.toV = v) }

theorem handshaking : (List.map g.degree g.V).sum = 2 * g.E.length := by
  sorry

end Problem12
