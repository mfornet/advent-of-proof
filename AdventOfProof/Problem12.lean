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

abbrev MultiGraph.Vertex : Type := Fin (g.numV)
instance : DecidableEq (MultiGraph.Vertex g) := inferInstanceAs (DecidableEq (Fin g.numV))
abbrev MultiGraph.Edge   : Type := DisjointPair (g.Vertex)

abbrev MultiGraph.V : List (g.Vertex) := List.finRange g.numV
def MultiGraph.connects (v : g.Vertex) (e : g.Edge) : Bool := Decidable.decide (e.fromV = v) ∨ Decidable.decide (e.toV = v)
def MultiGraph.degree' (E : List (g.Edge)) (v : g.Vertex) : Nat := List.length (List.filter (g.connects v) E)
def MultiGraph.degree (v : g.Vertex) : Nat := g.degree' g.E v

-- An edge with a direction, true means it goes in the direction [fromV -> toV] and false otherwise.
abbrev directedEdge := DisjointPair (g.Vertex) × Bool

-- set_option trace.Meta.synthInstance true
-- All edges that are directed out of a vertex v
def outEdges (v : g.Vertex) : Set (directedEdge g) :=
  { x | x.1 ∈ g.E ∧ (x.2 = true → x.1.fromV = v) ∧ (x.2 = false → x.1.toV = v) }

lemma List.filter_cons_length {a : α} {as : List α} {f : α → Bool} : ((List.filter f (a :: as)).length) = (List.filter f as |>.length) + (f a |>.toNat) := by?
  grind

theorem handshaking : (List.map g.degree g.V).sum = 2 * g.E.length := by
  obtain ⟨numV, E⟩ := g
  induction E with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero]
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x hx
    simp [MultiGraph.degree, MultiGraph.degree']
  | cons e es ih =>
    unfold MultiGraph.degree at ih ⊢
    unfold MultiGraph.degree' at ih ⊢
    simp [MultiGraph.V] at ih ⊢
    rw [Nat.mul_add, ← ih, mul_one]; clear ih
    conv =>
      lhs
      enter [1, 1]
      ext v
      rw [List.filter_cons_length]
    rw [List.sum_map_add]
    have tmp : (({ numV := numV, E := e :: es } : MultiGraph).connects) = (({ numV := numV, E := es } : MultiGraph).connects) := by
      ext v e₁
      simp [MultiGraph.connects]
    rw [tmp]; clear tmp
    simp [MultiGraph.connects]
    have disjoint_sum : ∀ v, (decide (e.fromV = v) || decide (e.toV = v)).toNat = (decide (e.fromV = v)).toNat + (decide (e.toV = v)).toNat := by
      intro v;
      by_cases h₁ : e.fromV = v
      · have this := e.diff
        grind
      by_cases h₂ : e.toV = v <;> grind
    conv =>
      enter [1, 1, 1]
      ext i
      rw [disjoint_sum]
    rw [List.sum_map_add, ← Fin.sum_univ_def, ← Fin.sum_univ_def]
    have sum_is_one : ∀ (a : Fin numV), ∑ i, (decide (a = i)).toNat = 1 := by
      intro a
      have tmp {x y : Fin numV}: (decide (x = y)).toNat = if x = y then (1 : Nat) else 0 := by grind
      conv =>
        enter [1, 2]
        ext i
        rw [tmp]
      rw [Fintype.sum_ite_eq]
    repeat rw [sum_is_one, sum_is_one]

end Problem12
