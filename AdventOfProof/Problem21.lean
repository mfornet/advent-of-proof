import Mathlib.Data.List.Basic

namespace Problem21

axiom Atom : Type

inductive L : Type where
| atom : Atom → L
| atomC : Atom → L
| times : L → L → L
| par : L → L → L
| bot : L
| one : L

notation "𝟙"=>L.one
notation "⊥"=>L.bot
infixl:30 " ⅋ "=>L.par
infixl:30 " ⊗ "=>L.times
notation "⟨" x "⟩"=> L.atom x
notation "⟨" x "⟩ᗮ"=> L.atomC x

@[simp]
def L.co : L → L
| ⟨ x ⟩ => ⟨ x ⟩ᗮ
| ⟨ x ⟩ᗮ => ⟨ x ⟩
| A ⊗ B => A.co ⅋ B.co
| A ⅋ B => A.co ⊗ B.co
| 𝟙 => ⊥
| ⊥ => 𝟙

postfix:70 "ᗮ"=>L.co

def L.pop (A B : L) : L := Aᗮ ⅋ B
infixr:30 "⊸"=>L.pop

inductive Deriv : List L → Prop where
| one      : Deriv [𝟙]
| identity : Deriv [ ⟨α⟩, ⟨α⟩ᗮ ]
| exch     : ∀ {Δ : List L}, (n : Fin Δ.length)
           → Deriv (Δ.get n :: Δ.eraseIdx (↑ n))
           → Deriv Δ
| times    : (n : Nat)
           → Deriv (A :: List.take n Δ)
           → Deriv (B :: List.drop n Δ)
           → Deriv ((A ⊗ B) :: Δ)
| par      : Deriv (A :: B :: Δ)
           → Deriv ((A ⅋ B) :: Δ)
| bottom   : Deriv Δ
           → Deriv (⊥ :: Δ)
| cut      : Deriv (A :: Δ)
           → Deriv (Aᗮ :: Γ)
           → Deriv (Δ ++ Γ)
prefix:10 "⊢"=> Deriv

instance : HasEquiv L where
  Equiv A B := (⊢ [A]) ↔ (⊢ [B])

attribute [simp] List.get
open Deriv

theorem lem₁ : ((A ⊗ B) ⊸ C) ≈ (A ⊸ (B ⊸ C))
  := by sorry
theorem lem₂ : (A ⊸ (B ⅋ C)) ≈ ((A ⊸ B) ⅋ C)
  := by sorry
theorem lem₃ : (A ⊸ B) ≈ (Bᗮ ⊸ Aᗮ)
  := by sorry

end Problem21
