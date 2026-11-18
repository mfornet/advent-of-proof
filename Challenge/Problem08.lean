-- Trusted Comparator challenge for Advent of Proof 2023, Q8.
-- Adapted from templates/Problem08.lean for Lean 4.30.
import Mathlib.Data.Vector.Basic 

namespace Problem8

inductive CompressedString : Nat → Type where 
| empty : CompressedString 0
| one   : Bool → (n : Nat) → CompressedString (Nat.succ n)
| cons  : (n : Nat) → CompressedString (Nat.succ m) → CompressedString (Nat.succ (Nat.succ (m + n)))

def head_c : CompressedString (Nat.succ n) → Bool 
| .one x n => x
| .cons _ str => not (head_c str)


def tail_c : CompressedString (Nat.succ n) → CompressedString n
| .one x c => match c with 
              | .zero => .empty
              | .succ n => .one x n
| .cons c str => match c with 
                 | .zero => str
                 | .succ n => .cons n str


def cons_c : Bool → CompressedString  n → CompressedString (Nat.succ n)
| b, .empty => .one b 0
| b, .one x n => if b = x 
               then .one x (Nat.succ n) 
               else .cons 0 (.one x n)
| b, .cons n str => if b = head_c (.cons n str) 
                  then .cons (Nat.succ n) str 
                  else .cons 0 (.cons n str)


@[simp]
def compress : {n : Nat} → List.Vector Bool n → CompressedString n
| .zero , _ => .empty
| .succ _ , v => cons_c (List.Vector.head v) (compress (List.Vector.tail v))

@[simp]
def decompress : ∀{n}, CompressedString n → List.Vector Bool n
| .zero, .empty => .nil
| .succ _, str => head_c str ::ᵥ decompress (tail_c str)


theorem prf₁ : ∀{n} (xs : CompressedString n), compress (decompress xs) = xs  := by
sorry

theorem prf₂ : ∀{n} (xs : List.Vector Bool n), decompress (compress xs) = xs := by
sorry

end Problem8
