import Mathlib.Tactic

namespace Problem10

axiom C : Type
axiom st : C → C → C
axiom op : C → C

infixl:65 " ⋆ " => st
postfix:max "ᵒ" => op

@[simp]
axiom assoc : ∀ a b c, a ⋆ (b ⋆ c) = (a ⋆ b) ⋆ c
axiom op_prop : ∀ a, a ⋆ aᵒ ⋆ a = a

noncomputable def co (x : C) : C := xᵒ ⋆ x ⋆ xᵒ
postfix:max "ᶜ" => co

theorem prop₁ : ∀ a, a ⋆ aᶜ ⋆ a = a
  := by simp [co, assoc, op_prop]

theorem prop₂ : ∀ a, aᶜ ⋆ a ⋆ aᶜ = aᶜ
  := by
  intro a
  simp [co, assoc]
  conv =>
    lhs
    arg 1; arg 1; arg 1
    rw [← assoc, ← assoc]
    arg 2
    rw [assoc, op_prop]
  conv =>
    lhs
    arg 1
    rw [← assoc, ← assoc]
    arg 2
    rw [assoc, op_prop]

axiom commute : ∀ a b, a ⋆ a = a → b ⋆ b = b → a ⋆ b = b ⋆ a

lemma ab_idem (p1 : a ⋆ b ⋆ a = a): a ⋆ b ⋆ (a ⋆ b) = a ⋆ b := by simp; rw [p1]

theorem uniqueness (p1 : a ⋆ z ⋆ a = a) (p2 : z ⋆ a ⋆ z = z) : z = aᶜ := by
  calc z = z ⋆ a ⋆ z := by grind
       _ = z ⋆ a ⋆ aᶜ ⋆ a ⋆ z := by nth_rewrite 1 [← prop₁ a]; simp
       _ = (z ⋆ a) ⋆ (aᶜ ⋆ a) ⋆ z := by simp
       _ = (aᶜ ⋆ a) ⋆ (z ⋆ a) ⋆ z := by rw [commute (aᶜ ⋆ a) (z ⋆ a) (ab_idem (prop₂ a)) (ab_idem p2)]
       _ = aᶜ ⋆ a ⋆ (z ⋆ a ⋆ z) := by simp
       _ = aᶜ ⋆ a ⋆ z := by rw [p2]
       _ = aᶜ ⋆ a ⋆ aᶜ ⋆ a ⋆ z := by nth_rewrite 1 [← prop₂ a]; simp
       _ = aᶜ ⋆ ((a ⋆ aᶜ) ⋆ (a ⋆ z)) := by simp
       _ = aᶜ ⋆ ((a ⋆ z) ⋆ (a ⋆ aᶜ)) := by rw [commute (a ⋆ aᶜ) (a ⋆ z) (ab_idem (prop₁ a)) (ab_idem p1)]
       _ = aᶜ ⋆ (a ⋆ z ⋆ a) ⋆ aᶜ := by simp
        _ = aᶜ ⋆ a ⋆ aᶜ := by rw [p1]
       _ = aᶜ := by rw [prop₂ a]

end Problem10
