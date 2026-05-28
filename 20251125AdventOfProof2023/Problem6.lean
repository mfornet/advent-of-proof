import Mathlib.Tactic

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

lemma execute_compile_cons  : execute (compile e ++ is) stack = execute is (execute (compile e) stack) := by
  induction' e generalizing stack is
  case Const x => simp [compile, execute, instr_semantics]
  case Plus e1 e2 hl hr => simp [compile]; repeat rw [hl, hr]; simp [execute]
  case Times e1 e2 hl hr => simp [compile]; repeat rw [hl, hr]; simp [execute]

theorem compile_correct_general : execute (compile e) stack = [ eval e ] ++ stack := by
  induction' e generalizing stack
  case Const x => simp [compile, execute, instr_semantics, eval]
  case Plus e1 e2 hl hr =>
    simp [eval, compile]
    rw [execute_compile_cons, execute_compile_cons]
    simp [execute, hl]
    rw [hr]
    simp [instr_semantics]
  case Times e1 e2 hl hr =>
    simp [eval, compile]
    rw [execute_compile_cons, execute_compile_cons]
    simp [execute, hl]
    rw [hr]
    simp [instr_semantics]

theorem compile_correct : execute (compile e) [] = [ eval e ] := by
  exact compile_correct_general
