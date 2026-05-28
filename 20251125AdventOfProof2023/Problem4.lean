import Mathlib.Tactic

namespace Problem4

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

def manhattan_spec : manhattan p q = Int.natAbs (q.1 - p.1) + Int.natAbs (q.2 - p.2) := by rfl
def up_spec : up p = (p.1, p.2 + 1) := by rfl
def down_spec : down p = (p.1, p.2 - 1) := by rfl
def left_spec : left p = (p.1 - 1, p.2) := by rfl
def right_spec : right p = (p.1 + 1, p.2) := by rfl

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

def manhattan_zero : manhattan p p = 0 := by
  simp [manhattan_spec]

def manhattan_succ_up : manhattan p q ≤ manhattan (up p) q + 1 := by
  simp [manhattan_spec, up_spec]
  suffices (q.2 - p.2).natAbs ≤ (q.2 - (p.2 + 1)).natAbs + 1 by linarith
  simp [helper_succ]

def manhattan_succ_down : manhattan p q ≤ manhattan (down p) q + 1 := by
  simp [manhattan_spec, down_spec]
  suffices (q.2 - p.2).natAbs ≤ (q.2 - (p.2 - 1)).natAbs + 1 by linarith
  simp [helper_pred]

def manhattan_succ_left : manhattan p q ≤ manhattan (left p) q + 1 := by
  simp [manhattan_spec, left_spec]
  suffices (q.1 - p.1).natAbs ≤ (q.1 - (p.1 - 1)).natAbs + 1 by linarith
  simp [helper_pred]

def manhattan_succ_right : manhattan p q ≤ manhattan (right p) q + 1 := by
  simp [manhattan_spec, right_spec]
  suffices (q.1 - p.1).natAbs ≤ (q.1 - (p.1 + 1)).natAbs + 1 by linarith
  simp [helper_succ]

theorem goal : ∀(path : OrthoPath p q), manhattan p q ≤ path_length path := by
  intro path
  induction' path
  case move_up p' q' path ih =>
    simp [path_length]
    calc manhattan p' q' ≤ manhattan (up p') q' + 1 := by exact manhattan_succ_up
                      _ ≤ path_length path + 1 := by linarith
  case move_down p' q' path ih =>
    simp [path_length]
    calc manhattan p' q' ≤ manhattan (down p') q' + 1 := by exact manhattan_succ_down
                      _ ≤ path_length path + 1 := by linarith
  case move_left p' q' path ih =>
    simp [path_length]
    calc manhattan p' q' ≤ manhattan (left p') q' + 1 := by exact manhattan_succ_left
                      _ ≤ path_length path + 1 := by linarith
  case move_right p' q' path ih =>
    simp [path_length]
    calc manhattan p' q' ≤ manhattan (right p') q' + 1 := by exact manhattan_succ_right
                      _ ≤ path_length path + 1 := by linarith
  case stop p' =>
    rw [manhattan_zero]
    exact Nat.zero_le _

end Problem4
