import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.MapLemmas
import Mathlib.Tactic

namespace Problem15

-- Just patching a hole in mathlib..
def List.Vector.finRange (n : Nat) : List.Vector (Fin n) n := List.Vector.ofFn id

lemma List.Vector.finRange_get (i : Fin n)
    : List.Vector.get (List.Vector.finRange n) i = i := by
  simp [List.Vector.finRange]

-- We use the PSigma dependent pair because the left side is computational and the right side is just a Prop.
def Sur (v : List.Vector (Fin n) n) : Type := (x : Fin n) → Σ' i, v.get i = x

def Inj (v : List.Vector (Fin n) n) : Prop := ∀ (a b : Fin n), v.get a = v.get b → a = b

structure Perm (n : Nat) : Type where
  indices : List.Vector (Fin n) n
  surjective : Sur indices
  injective : Inj indices

-- These lemmas are just assumed in Agda because of its janky handling of proof irrelevance
-- But we can prove it in Lean!
lemma sur_irrelevant (inj : Inj indices) (a b : Sur indices) : a = b := by
  apply funext; intro x; cases (a x); cases (b x); congr; apply inj; simp [*]

lemma cong_Perm (p q : Perm n) : p.indices = q.indices → p = q := by
  intro eq; cases p; cases q; simp at *; cases eq; simp; apply sur_irrelevant; trivial
-- You can use cong_Perm to prove the associativity, identity and inverse laws below.

@[simp]
def permute (p : Perm n) (v : List.Vector A n) : List.Vector A n := p.indices.map v.get

def comp (p q : Perm n) : Perm n where
  indices := List.Vector.ofFn (p.indices.get ∘ q.indices.get)
  injective : Inj (List.Vector.ofFn (p.indices.get ∘ q.indices.get)) := by
    intro a b h
    simp only [List.Vector.get_ofFn, Function.comp_apply] at h
    apply p.injective at h
    apply q.injective at h
    assumption
  surjective : Sur (List.Vector.ofFn (p.indices.get ∘ q.indices.get)) := by
    intro x
    simp [List.Vector.get_ofFn]
    obtain ⟨pi, hp⟩ := p.surjective x
    obtain ⟨qi, hq⟩ := q.surjective pi
    use qi
    grind

@[ext] theorem perm_ext {p₁ p₂ : Perm n} (h : ∀ i, p₁.indices.get i = p₂.indices.get i): p₁ = p₂ := by
  suffices p₁.indices = p₂.indices by
    exact cong_Perm p₁ p₂ this
  ext i
  grind

infixl:60 " ⊡ " => comp

theorem composition (v : List.Vector A n) (p q : Perm n)
    : permute (p ⊡ q) v = permute q (permute p v) := by
  simp [permute]
  ext i
  simp [comp]

theorem assoc (p q r : Perm n) : p ⊡ (q ⊡ r) = p ⊡ q ⊡ r := by
  ext i
  simp [comp]

def ι : Perm n where
  indices := List.Vector.finRange n
  injective := by
    intro a b
    rw [List.Vector.finRange_get, List.Vector.finRange_get]
    grind
  surjective := by
    intro x
    use x
    rw [List.Vector.finRange_get]

theorem identity_l (p : Perm n) : ι ⊡ p = p := by
  ext i
  simp [comp, ι]
  rw [List.Vector.finRange_get]

theorem identity_r (p : Perm n) : p ⊡ ι = p := by
  ext i
  simp [comp, ι]
  rw [List.Vector.finRange_get]

def inv (p : Perm n) : Perm n where
  indices := List.Vector.ofFn (fun x => p.surjective x |>.1)
  injective := by
    intro a b h
    simp at h
    rw [← (p.surjective a |>.snd), ← (p.surjective b |>.snd), h]
  surjective := by
    intro x
    simp
    -- use p.surjective x |>.fst
    -- suffices p.indices.get (p.surjective (p.surjective x).fst).fst = p.indices.get x by
    --   apply p.injective ((p.surjective (p.surjective x).fst).fst) x
    --   assumption
    -- rw [p.surjective (p.surjective x |>.fst) |>.snd]



    sorry

postfix:65 "⁻¹" => inv

theorem inverse_l (p : Perm n) : p ⁻¹ ⊡ p = ι := by
  sorry

theorem inverse_r (p : Perm n) : p ⊡ p ⁻¹ = ι := by
  sorry

end Problem15
