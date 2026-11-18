-- Trusted Comparator challenge for Advent of Proof 2023, Q24.
-- Adapted from templates/Problem24.lean for Lean 4.30.
import Mathlib.Tactic

namespace Problem24

-- Mathlib already has something called Tree
inductive Tree' : Type where
| leaf : Tree'
| branch : Tree' → Tree' → Tree'

def toList (d : Nat) : Tree' → List Nat
| .leaf => [d]
| .branch t₁ t₂ => toList d.succ t₁ ++ toList d.succ t₂

theorem toList_injective : toList n t = toList n t' → t = t' 
  := by sorry

end Problem24
