import Mathlib.Tactic

namespace Problem2

variable {T : Type}

def Relation (T : Type) := (T → T → Prop)

def Commutes (R1 R2 : Relation T) : Prop :=
  ∀{x y z}, R1 x y → R2 x z → ∃ t, R2 y t ∧ R1 z t

def Diamond (R : Relation T) : Prop := Commutes R R

inductive Star (R : Relation T) : Relation T where
| rule  : ∀ {x y}, R x y → Star R x y
| refl  : ∀ {x}, Star R x x
| trans : ∀ {x y z}, Star R x y → Star R y z → Star R x z

def MyRelation : Relation Nat := fun _ _ => False

theorem strip  : ∀ {R : Relation T}, Diamond R → Commutes (Star R) R := by
  intro r d x y z s hxz
  induction' s generalizing z
  case rule x1 y1 h =>
    have ⟨t, ht⟩ := d h hxz
    exact Exists.intro t (And.intro ht.1 (Star.rule ht.2))
  case refl x1 =>
    use z
    constructor
    · exact hxz
    · exact Star.refl
  case trans x1 y1 z1 h1 h2 ih1 ih2 =>
    specialize ih1 hxz
    obtain ⟨t1, ht1⟩ := ih1
    specialize ih2 ht1.1
    obtain ⟨t2, ht2⟩ := ih2
    use t2
    constructor
    · exact ht2.1
    · exact Star.trans ht1.2 ht2.2

end Problem2
