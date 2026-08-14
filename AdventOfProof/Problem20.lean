import Mathlib

namespace Problem20

inductive Expr : Type → Type 1
| lam : Expr (Option V) → Expr V
| app : Expr V → Expr V → Expr V
| var : V → Expr V

@[simp]
def Expr.map (f : A → B): Expr A → Expr B
| .lam e     => .lam (e.map (Option.map f))
| .app e₁ e₂ => .app (e₁.map f) (e₂.map f)
| .var v     => .var (f v)

@[simp]
def lift (f : A → Expr B) : Option A → Expr (Option B)
| .some x => (f x).map Option.some
| .none   => .var (Option.none)

@[simp]
def Expr.bind (f : A → Expr B) : Expr A → Expr B
| .lam e     => .lam (e.bind (lift f))
| .app e₁ e₂ => .app (e₁.bind f) (e₂.bind f)
| .var v     => f v

theorem identₗ (f : A → Expr B)(x : A) : (Expr.var x).bind f = f x
  := by simp

theorem identᵣ (e : Expr A) : e.bind Expr.var = e
  := by sorry

theorem assoc (g : A → Expr B)(h : B → Expr C)(a : Expr A) :
        a.bind (fun a' => (g a').bind h) = (a.bind g).bind h
  := by sorry

end Problem20
