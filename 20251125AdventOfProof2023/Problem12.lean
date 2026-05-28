import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

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

theorem handshaking : (List.map g.degree g.V).sum = 2 * g.E.length := by sorry

end Problem12
