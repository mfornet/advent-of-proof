import Mathlib.Data.Vector
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.Fin

class MoreThanOne (n : Nat) : Prop where
  mto : n > 1

instance [MoreThanOne n] : NeZero n where
   out := by rename_i inst; cases inst; rename_i l; cases l; simp; simp

def toRadix (n : Nat)[MoreThanOne n] : (f : Nat) → Nat → Vector (Fin n) f
| 0 , _ => Vector.nil
| .succ f , k => let (q , r) := (Nat.divModEquiv n) k; Vector.cons r (toRadix n f q)

def fromRadix (n : Nat) : {f : Nat} → Vector (Fin n) f → Nat
| .zero, Vector.nil => 0
| .succ _, v => (↑ (Vector.head v)) + (n * fromRadix n (Vector.tail v))

theorem goal₁ (n : Nat)[MoreThanOne n](f : Nat)(num : Vector (Fin n) f) : 
              toRadix n f (fromRadix n num) = num 
  := by sorry

theorem goal₂ (n : Nat)[MoreThanOne n](f : Nat)(k : Nat)(bound : k < n ^ f) : 
              fromRadix n (toRadix n f k) = k
  := by sorry