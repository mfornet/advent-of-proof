import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.MapLemmas
import Mathlib.Tactic

namespace Problem15

-- Just patching a hole in mathlib..
def List.Vector.finRange (n : Nat) : List.Vector (Fin n) n := List.Vector.ofFn id
lemma List.Vector.finRange_get (i : Fin n) : List.Vector.get (List.Vector.finRange n) i = i := by
  simp [List.Vector.finRange]

-- We use the PSigma dependent pair because the left side is computational and the right side is just a Prop.
def Sur (v : List.Vector (Fin n) n) : Type := (x : Fin n) →  Σ' i, v.get i = x
def Inj (v : List.Vector (Fin n) n) : Prop := ∀(a b : Fin n), v.get a = v.get b → a = b

structure Perm (n : Nat) : Type where
  indices : List.Vector (Fin n) n

  surjective : Sur indices
  injective : Inj indices

-- These lemmas are just assumed in Agda because of its janky handling of proof irrelevance
-- But we can prove it in Lean!
lemma sur_irrelevant (inj : Inj indices)(a b : Sur indices) : a = b := by
  apply funext; intro x; cases (a x); cases (b x); congr; apply inj; simp [*]
lemma cong_Perm (p q : Perm n) : p.indices = q.indices → p = q := by
  intro eq; cases p; cases q; simp at *; cases eq; simp; apply sur_irrelevant; trivial
-- You can use cong_Perm to prove the associativity, identity and inverse laws below.

@[simp]
def permute (p : Perm n) (v : List.Vector A n) : List.Vector A n := p.indices.map v.get

def comp (p q : Perm n) : Perm n where
  indices := List.Vector.ofFn (p.indices.get ∘ q.indices.get)
  injective : Inj (List.Vector.ofFn (p.indices.get ∘ q.indices.get)) := by
    sorry
  surjective : Sur (List.Vector.ofFn (p.indices.get ∘ q.indices.get)) := by
    sorry
infixl:60 " ⊡ "=>comp

theorem composition (v : List.Vector A n)(p q : Perm n) : permute (p ⊡ q) v = permute q (permute p v) := by
  sorry

theorem assoc (p q r : Perm n) : p ⊡ (q ⊡ r) = p ⊡ q ⊡ r := by
  sorry

def ι : Perm n where
  indices := List.Vector.finRange n
  injective := by sorry
  surjective := by sorry

theorem identity_l (p : Perm n) : ι ⊡ p = p := by
  sorry

theorem identity_r (p : Perm n) : p ⊡ ι  = p := by
  sorry

def inv ( p : Perm n) : Perm n where
  indices := sorry
  injective := by sorry
  surjective := by sorry

postfix:65 "⁻¹" => inv

theorem inverse_l (p : Perm n) : p ⁻¹ ⊡ p = ι := by
  sorry
theorem inverse_r (p : Perm n) : p ⊡ p ⁻¹ = ι := by
  sorry

end Problem15
