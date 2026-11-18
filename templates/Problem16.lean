import Mathlib
def Inj (f : Fin n → Fin n) : Prop := ∀ i j, f i = f j → i = j
def Sur (f : Fin n → Fin n) : Prop := ∀ x, ∃ y, f y = x

theorem goal (n : Nat)(f : Fin n → Fin n) : Inj f → Sur f := by 
  sorry