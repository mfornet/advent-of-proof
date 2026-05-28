import Mathlib.Tactic

inductive B : Type
| T : B
| F : B

def iterate : Nat → (B → B) → B → B
  | 0 , _, b => b
  | Nat.succ n , f, b => f (iterate n f b)

def twice : (B → B) → B → B := iterate 2

#eval 10

def goal : ∀ (f : B → B) (b : B) (n : Nat), iterate n (twice f) (f b) = f b := by
  sorry
