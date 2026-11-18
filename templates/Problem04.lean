import Std.Data.Int.Lemmas

def Point : Type := Int × Int

def up : Point → Point 
| ( x , y ) => (x , y + 1)
def down : Point → Point 
| ( x , y ) => (x , y - 1)
def left : Point → Point 
| ( x , y ) => (x - 1 , y)
def right : Point → Point 
| ( x , y ) => (x + 1 , y)

inductive OrthoPath : Point → Point → Type where 
| move_up    : OrthoPath (up p) q → OrthoPath p q 
| move_down  : OrthoPath (down p) q → OrthoPath p q 
| move_left  : OrthoPath (left p) q → OrthoPath p q 
| move_right : OrthoPath (right p) q → OrthoPath p q 
| stop       : OrthoPath p p

def path_length : OrthoPath p q → Nat
| .move_up p    => .succ (path_length p)
| .move_down p  => .succ (path_length p)
| .move_left p  => .succ (path_length p)
| .move_right p => .succ (path_length p)
| .stop => 0

def manhattan : Point → Point → Nat
| (x₁ , y₁), (x₂ , y₂) => Int.natAbs (x₂ - x₁) + Int.natAbs (y₂ - y₁)

theorem helper_succ : Int.natAbs (a - b) ≤ Nat.succ (Int.natAbs (a - (b + 1))) := by
  have proof := Int.natAbs_add_le (a - (b+1)) 1
  have h : a - (b+1) + 1 = a-b := by
    rw [ Int.sub_eq_add_neg, Int.neg_add, Int.add_assoc, Int.add_assoc, Int.add_comm (-1) 1,
         ←Int.sub_eq_add_neg, Int.sub_self, Int.add_zero, ←Int.sub_eq_add_neg ]
  rw [h] at proof
  exact proof
theorem helper_pred : Int.natAbs (a - b) ≤ Nat.succ (Int.natAbs (a - (b - 1))) := by
  have proof := Int.natAbs_add_le (a - (b-1)) (-1)
  have h : a - (b-1) + -1 = a-b := by
    rw [ Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.neg_add, Int.neg_neg, Int.add_assoc, 
         Int.add_assoc, ←Int.sub_eq_add_neg, Int.sub_self, Int.add_zero, ←Int.sub_eq_add_neg ]
  rw [h] at proof
  exact proof

-- the following theorems proved useful
-- Nat.add_succ Nat.succ_add Nat.add_le_add Nat.succ_le_succ

theorem goal : ∀(path : OrthoPath p q), manhattan p q ≤ path_length path := by
sorry