-- Trusted Comparator challenge for Advent of Proof 2023, Q6.
-- Adapted from templates/Problem06.lean for Lean 4.30.

namespace Problem6

inductive Expr : Type where
| Const : Nat → Expr
| Plus  : Expr → Expr → Expr
| Times : Expr → Expr → Expr

def eval : Expr → Nat
| .Const n => n
| .Plus  e1 e2 => eval e1 + eval e2
| .Times e1 e2 => eval e1 * eval e2

inductive Instr : Type where 
| Push : Nat → Instr
| Add  : Instr
| Mult : Instr

def instr_semantics : Instr → (List Nat → List Nat)
| .Push n, s => n :: s  
| .Add,  y :: x :: s => (x + y) :: s 
| .Mult, y :: x :: s => (x * y) :: s 
| _, _ => []

def execute : List Instr → List Nat → List Nat
| [],        s => s
| (i :: is), s => execute is (instr_semantics i s)

def compile : Expr → List Instr 
| .Const x => [ .Push x ]
| .Plus  e1 e2 => compile e1 ++ compile e2 ++ [ .Add  ]
| .Times e1 e2 => compile e1 ++ compile e2 ++ [ .Mult ]

theorem compile_correct : execute (compile e) [] = [ eval e ] := by 
sorry

end Problem6
