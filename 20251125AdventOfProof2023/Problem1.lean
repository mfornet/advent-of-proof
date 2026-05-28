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
  induction' n
  · case zero => simp [iterate]
  · case succ n ih =>
      simp [iterate]; rw [ih]; clear ih
      simp [twice, iterate]

      cases hb : b
      · set ft := f B.T
        cases ht : ft
        · grind
        · set ff := f B.F
          cases hf : ff
          · grind
          · grind
      · set ff := f B.F
        cases ht : ff
        · set ft := f B.T
          cases hf : ft
          · grind
          · grind
        · grind

end Problem1
