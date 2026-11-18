inductive Term : Type where
| Ref : Term 
| Sop : Term
| Kop : Term 
| App : Term → Term → Term


inductive reduces : Term → Term → Prop where
| red_S : ∀ {M N P}, reduces (.App (.App (.App .Sop M) N) P) (.App (.App M P) (.App N P))
| red_K : ∀ {M N}, reduces (.App (.App .Kop M) N) M 
| red_left : ∀ {M1 M2 N}, reduces M1 M2 → reduces (.App M1 N) (.App M2 N)
| red_right : ∀ {M N1 N2}, reduces N1 N2 → reduces (.App M N1) (.App M N2)
| red_trans : ∀ {M N P}, reduces M N → reduces N P → reduces M P
infixl:60 " ↦ "=> reduces

def ident : Term := sorry
theorem ident_red : .App ident M ↦ M := sorry

def const_sop : Term := sorry
theorem const_sop_red : .App const_sop M ↦ .Sop := sorry

def const_kop : Term := sorry
theorem const_kop_red : ∀ M, .App const_kop M ↦ .Kop := sorry

def app_app (M₁ : Term)(M₂ : Term) : Term := sorry
theorem app_app_red : ∀ M₁ M₂ M₃, .App (app_app M₁ M₂) M₃ ↦ .App (.App M₁ M₃) (.App M₂ M₃) := sorry


def substitution : Term → Term → Term
| .Ref, N => N
| .Sop, _ => .Sop 
| .Kop, _ => .Kop
| .App M₁ M₂, N => .App (substitution M₁ N) (substitution M₂ N)

def lambda : Term → Term := sorry

theorem beta : ∀ M N, .App (lambda M) N ↦ substitution M N := sorry