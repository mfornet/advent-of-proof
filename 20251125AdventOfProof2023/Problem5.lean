inductive Symbol : Type where
| O : Symbol
| C : Symbol

inductive M : List Symbol → Type where
| empty : M []
| juxt  : M a → M b → M (a ++ b)
| nest  : M a → M (Symbol.O :: a ++ [ Symbol.C ])

inductive ListOf (P : List Symbol → Type) : List Symbol → Type where
| empty : ListOf P []
| cons  : P a → ListOf P b → ListOf P (a ++ b)

inductive N : List Symbol → Type where
| nest : ListOf N a → N (Symbol.O :: a ++ [ Symbol.C ])

def L := ListOf N

def goal : M s → L s := by
  sorry

-- Lean's support for mutual induction is terrible!
-- Serious bonus points for anyone who can prove this one:
-- theorem goal : L s → M s := by sorry
