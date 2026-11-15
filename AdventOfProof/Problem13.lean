import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace Problem13
open scoped Fin.NatCast

class MoreThanOne (n : Nat) : Prop where
  mto : n > 1

instance [MoreThanOne n] : NeZero n where
  out := by rename_i inst; cases inst; rename_i l; cases l; simp; simp

def toRadix (n : Nat) [MoreThanOne n] : (f : Nat) → Nat → List.Vector (Fin n) f
  | 0, _ => List.Vector.nil
  | .succ f, k =>
      let (q, r) := (Nat.divModEquiv n) k
      List.Vector.cons r (toRadix n f q)

def fromRadix (n : Nat) : {f : Nat} → List.Vector (Fin n) f → Nat
  | .zero, List.Vector.nil => 0
  | .succ _, v => (List.Vector.head v) + (n * fromRadix n (List.Vector.tail v))

lemma tmp {a b n : Nat} (h : n > 0) : (a + n * b) / n = a / n + b := Nat.add_mul_div_left a b h

theorem goal₁ (n : Nat) [MoreThanOne n] (f : Nat) (num : List.Vector (Fin n) f)
    : toRadix n f (fromRadix n num) = num := by
  induction f with
  | zero =>
    have h : num = List.Vector.nil := by exact List.Vector.eq_nil num
    subst h
    simp [toRadix]
  | succ f ih =>
    simp [toRadix]
    specialize ih num.tail
    have h : fromRadix n num / n = fromRadix n (f := f) num.tail := by
      conv_lhs =>
        unfold fromRadix
      have mto : n > 1 := MoreThanOne.mto
      rw [Nat.add_mul_div_left _ _ (by grind)]
      simp
    rw [h, ih]
    suffices Nat.cast (fromRadix n num) = num.head by
      rw [this]
      exact List.Vector.cons_head_tail num
    simp [fromRadix]
    apply Fin.ext
    rw [Fin.val_natCast]
    simp only [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt num.head.isLt

theorem goal₂ (n : Nat) [MoreThanOne n] (f : Nat) (k : Nat) (bound : k < n ^ f)
    : fromRadix n (toRadix n f k) = k := by
  induction f generalizing k with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at bound
    subst bound
    simp [toRadix, fromRadix]
  | succ f ih =>
    simp [toRadix, fromRadix]
    have h' : k / n < n ^ f := by
      refine (Nat.div_lt_iff_lt_mul ?_).mpr bound
      grind
    specialize ih (k / n) h'
    rw [ih]
    exact Nat.mod_add_div k n

end Problem13
