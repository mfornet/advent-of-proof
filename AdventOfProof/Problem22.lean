import Mathlib.Tactic

namespace Problem22

axiom State : Type
axiom Act : Type
axiom step : State → Act → State → Prop

notation q1:60 "─⟨" a "⟩→" q2:60 => step q1 a q2

structure Bisimulation (R : State → State → Prop) : Prop where
  left  : R x y → x ─⟨ α ⟩→ x' → ∃ y', y ─⟨ α ⟩→ y' ∧ R x' y'
  right : R x y → y ─⟨ α ⟩→ y' → ∃ x', x ─⟨ α ⟩→ x' ∧ R x' y'

def bisimilar (q₁ q₂ : State) : Prop := ∃ R, Bisimulation R ∧ R q₁ q₂
infixl:60 " ≡ᵇ " => bisimilar

theorem reflexive : x ≡ᵇ x
   := by sorry
theorem symmetric : x ≡ᵇ y → y ≡ᵇ x
   := by sorry
theorem transitive : x ≡ᵇ y → y ≡ᵇ z → x ≡ᵇ z
   := by sorry
theorem bisim_is_bisim : Bisimulation bisimilar
   := by sorry

inductive HML : Type where
| Exi : Act → HML → HML
| All : Act → HML → HML
| And : HML → HML → HML
| Top : HML
| Not : HML → HML

notation "⟪" α "⟫ " φ => HML.Exi α φ
notation "⟦" α "⟧ " φ => HML.All α φ
infixl:60 " & " => HML.And
notation "⊤" => HML.Top
postfix:50 "ᗮ" => HML.Not

def HML.models (σ : State): HML → Prop
| ⊤ => True
| φᗮ => ¬ (HML.models σ φ)
| φ & ψ => (HML.models σ φ) ∧ (HML.models σ ψ)
| ⟪α⟫ φ => ∃ σ', σ ─⟨ α ⟩→ σ' ∧ HML.models σ' φ
| ⟦α⟧ φ => ∀ σ', σ ─⟨ α ⟩→ σ' → HML.models σ' φ
infix:70 " ⊧ " => HML.models


theorem hml_bisim (b : x ≡ᵇ y) : ∀ φ, x ⊧ φ → y ⊧ φ
  := by sorry

end Problem22
