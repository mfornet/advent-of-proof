-- Trusted Comparator challenge for Advent of Proof 2023, Q16.
-- Adapted from templates/Problem16.lean for Lean 4.30.
import Mathlib

namespace Problem16

def Inj (f : Fin n → Fin n) : Prop := ∀ i j, f i = f j → i = j
def Sur (f : Fin n → Fin n) : Prop := ∀ x, ∃ y, f y = x

theorem goal (n : Nat)(f : Fin n → Fin n) : Inj f → Sur f := by 
  sorry

end Problem16
