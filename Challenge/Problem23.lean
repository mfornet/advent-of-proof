-- Trusted Comparator challenge for Advent of Proof 2023, Q23.
-- Adapted from templates/Problem23.lean for Lean 4.30.
import Mathlib

namespace Problem23

def Assertion (State : Type) : Type := State → Prop

def conjₐ (φ ψ : Assertion State) : Assertion State := fun σ => φ σ ∧ ψ σ
infixl:60 " ∧' " => conjₐ
def negₐ (φ : Assertion State) : Assertion State := fun σ => ¬ φ σ
prefix:90 " ¬' " => negₐ
def implₐ (φ ψ : Assertion State) : Prop := ∀ σ, φ σ → ψ σ
infixr:80 " ⇒ " => implₐ

inductive Program (State : Type) : Type where
| SKIP : Program State
| ITE  : Assertion State → Program State → Program State → Program State
| LOOP : Assertion State → Program State → Program State
| SEQ  : Program State → Program State → Program State
| UPD  : (State → State) → Program State
open Program
notation "IF" a "THEN" b "ELSE" c "FI" => ITE a b c
notation "WHILE" a "DO" b "OD" => LOOP a b
infixl:40 " ∶ " => SEQ

inductive Triple : Assertion State → Program State → Assertion State → Prop where 
| skipₕ : Triple φ SKIP φ
| ifₕ : Triple (φ ∧' g) P ψ → Triple (φ ∧' (¬' g)) Q ψ → Triple φ (IF g THEN P ELSE Q FI) ψ
| whileₕ : Triple (φ ∧' g) P φ → Triple φ (WHILE g DO P OD) (φ ∧' (¬' g))
| seqₕ : Triple π Q ψ → Triple φ P π → Triple φ (P ∶ Q) ψ
| updₕ : Triple (φ ∘ f) (Program.UPD f) φ
| conseqₕ : φ ⇒ φ' → ψ' ⇒ ψ → Triple φ' P ψ' → Triple φ P ψ

structure ListSum : Type where
  A : List Nat
  s : Nat
  i : Nat

def prog : Program ListSum := 
    UPD (fun σ => { σ with i := 0 })
  ∶ UPD (fun σ => { σ with s := 0 })
  ∶ WHILE (fun σ => σ.i ≠ σ.A.length) DO 
      UPD (fun σ => { σ with s := σ.s + σ.A.getD σ.i 0})
    ∶ UPD (fun σ => { σ with i := σ.i.succ})
    OD

theorem goal : Triple (fun σ => A₀ = σ.A) prog (fun σ => σ.s =  A₀.sum) 
  := by sorry

end Problem23
