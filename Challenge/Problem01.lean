-- Trusted Comparator challenge for Advent of Proof 2023, Q1.
-- Adapted from templates/Problem01.lean for Lean 4.30.

namespace Problem1

inductive B : Type
| T : B
| F : B

def iterate : Nat → (B → B) → B → B
  | 0 , _, b => b
  | Nat.succ n , f, b => f (iterate n f b)

def twice : (B → B) → B → B := iterate 2

def goal : ∀ (f : B → B) (b : B) (n : Nat), iterate n (twice f) (f b) = f b := by
sorry

end Problem1
