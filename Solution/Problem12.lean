import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin

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
def MultiGraph.Connects (v : g.Vertex) (e : g.Edge) : Prop := e.fromV = v ∨ e.toV = v
def MultiGraph.connects (v : g.Vertex) (e : g.Edge) : Bool := Decidable.decide (e.fromV = v) ∨ Decidable.decide (e.toV = v)
def MultiGraph.degree' (E : List (g.Edge)) (v : g.Vertex) : Nat := List.length (List.filter (g.connects v) E)
def MultiGraph.degree (v : g.Vertex) : Nat := g.degree' g.E v

-- An edge with a direction, true means it goes in the direction [fromV -> toV] and false otherwise.
abbrev directedEdge := DisjointPair (g.Vertex) × Bool

-- set_option trace.Meta.synthInstance true
-- All edges that are directed out of a vertex v
def outEdges (v : g.Vertex) : Set (directedEdge g) :=
  { x | x.1 ∈ g.E ∧ (x.2 = true → x.1.fromV = v) ∧ (x.2 = false → x.1.toV = v) }

theorem connects_sum (e : g.Edge) : (g.V.map fun v => (g.connects v e).toNat).sum = 2 := by
  have := e.diff
  have h : ∀ v, (g.connects v e).toNat
      = (if e.fromV = v then 1 else 0) + (if e.toV = v then 1 else 0) := by
    intro v; simp only [MultiGraph.connects]; grind
  change (List.map (fun v : Fin g.numV => (g.connects v e).toNat) (List.finRange g.numV)).sum = 2
  rw [← Fin.sum_univ_def]
  simp only [MultiGraph.Vertex, h, Finset.sum_add_distrib]
  change (∑ x : Fin g.numV, if e.fromV = x then (1 : Nat) else 0) +
    (∑ x : Fin g.numV, if e.toV = x then (1 : Nat) else 0) = 2
  have hfrom : (∑ x : Fin g.numV, if e.fromV = x then (1 : Nat) else 0) = 1 := by
    exact Fintype.sum_ite_eq (ι := Fin g.numV) (e.fromV : Fin g.numV) (fun _ => (1 : Nat))
  have hto : (∑ x : Fin g.numV, if e.toV = x then (1 : Nat) else 0) = 1 := by
    exact Fintype.sum_ite_eq (ι := Fin g.numV) (e.toV : Fin g.numV) (fun _ => (1 : Nat))
  rw [hfrom, hto]

theorem degree'_nil : g.degree' [] = fun _ => 0 := rfl

theorem degree'_cons (e : g.Edge) (es : List g.Edge) :
    g.degree' (e :: es) = fun v => g.degree' es v + (g.connects v e).toNat := by
  funext v; simp only [MultiGraph.degree', List.filter_cons]; split <;> simp_all

theorem handshaking' (L : List g.Edge) :
    (g.V.map (g.degree' L)).sum = 2 * L.length := by
  induction L with
  | nil => simp [degree'_nil]
  | cons e es ih =>
    rw [degree'_cons, List.sum_map_add, ih, connects_sum, List.length_cons]
    omega

theorem handshaking : (List.map g.degree g.V).sum = 2 * g.E.length :=
  handshaking' g g.E

end Problem12
