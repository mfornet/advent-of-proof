import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Problem13

class MoreThanOne (n : Nat) : Prop where
  mto : n > 1

instance [MoreThanOne n] : NeZero n where
   out := by rename_i inst; cases inst; rename_i l; cases l; simp; simp

def toRadix (n : Nat)[MoreThanOne n] : (f : Nat) → Nat → List.Vector (Fin n) f
| 0 , _ => List.Vector.nil
| .succ f , k => let (q , r) := (Nat.divModEquiv n) k; List.Vector.cons r (toRadix n f q)

def fromRadix (n : Nat) : {f : Nat} → List.Vector (Fin n) f → Nat
| .zero, List.Vector.nil => 0
| .succ _, v => (↑ (List.Vector.head v)) + (n * fromRadix n (List.Vector.tail v))

theorem goal₁ (n : Nat)[MoreThanOne n](f : Nat)(num : List.Vector (Fin n) f) :
              toRadix n f (fromRadix n num) = num
  := by sorry

theorem goal₂ (n : Nat)[MoreThanOne n](f : Nat)(k : Nat)(bound : k < n ^ f) :
              fromRadix n (toRadix n f k) = k
  := by sorry

end Problem13
