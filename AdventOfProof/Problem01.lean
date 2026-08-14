import Mathlib.Tactic

namespace Problem1

inductive B : Type
| T : B
| F : B

def iterate : Nat → (B → B) → B → B
  | 0 , _, b => b
  | Nat.succ n , f, b => f (iterate n f b)

def twice : (B → B) → B → B := iterate 2

def goal : ∀ (f : B → B) (b : B) (n : Nat), iterate n (twice f) (f b) = f b := by
  intro f b n
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      simp [iterate]; rw [ih]; clear ih
      simp [twice, iterate]
      cases b <;> cases hT : f B.T <;> cases hF : f B.F <;> grind


end Problem1
