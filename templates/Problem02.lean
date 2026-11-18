variable {T : Type}
def Relation (T : Type) := (T → T → Prop)

def Commutes (R1 R2 : Relation T) : Prop :=
  ∀{x y z}, R1 x y → R2 x z → ∃ t, R2 y t ∧ R1 z t

def Diamond (R : Relation T) : Prop := Commutes R R

inductive Star (R : Relation T) : Relation T where 
| rule  : ∀ {x y}, R x y → Star R x y
| refl  : ∀ {x}, Star R x x
| trans : ∀ {x y z}, Star R x y → Star R y z → Star R x z

theorem strip  : ∀{R : Relation T}, Diamond R → Commutes (Star R) R := by
sorry 
