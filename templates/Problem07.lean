axiom T : Type
axiom f : T → T

-- marked noncomputable as f may be noncomputable
@[simp]
noncomputable def tortoise (p : T × T) : T × T := (f p.1, p.2)
@[simp]
noncomputable def hare (p : T × T) : T × T := (p.1, f p.2)

inductive Run : T × T → (length : Nat) → Prop where
| empty : Run (c , c) 0
| step  : Run (tortoise p) n → Run p (Nat.succ n) 

@[simp]
def Loop (n : Nat) : Prop := ∃ c : T, Run (c , c) n

noncomputable def race (p : T × T) : T × T := hare (hare (tortoise p))

theorem goal : Nat.repeat race n (x , x) = (c, c) → Loop n := by 
sorry
