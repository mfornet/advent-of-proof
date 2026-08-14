import Mathlib.Data.Vector.Basic

namespace Problem18

axiom Symbol : Type

inductive Patch : Nat → Nat → Type
| end : Patch 0 0
| skp : Patch n m → Patch n.succ m.succ
| del : Patch n m → Patch n.succ m
| ins : Symbol → Patch n m → Patch n m.succ

def Patch.apply : Patch n m → List.Vector Symbol n → List.Vector Symbol m
| .end     , vec => vec
| .del p   , vec => p.apply vec.tail
| .skp p   , vec => List.Vector.cons vec.head (p.apply vec.tail)
| .ins x p , vec => List.Vector.cons x (p.apply vec)

def Patch.compose : Patch a b → Patch b c → Patch a c
| .end , p₂ => p₂
| .skp p₁ , .skp p₂ => .skp (compose p₁ p₂)
| .skp p₁ , .del p₂ => .del (compose p₁ p₂)
| .skp p₁ , .ins x p₂ => .ins x (compose (.skp p₁) p₂)
| .ins x p₁ , .ins x₂ p₂ => .ins x₂ (compose (.ins x p₁) p₂)
| .del p₁ , .ins x₂ p₂ => .ins x₂ (compose (.del p₁) p₂)
| .del p₁ , .skp p₂ => .del (compose p₁ (.skp p₂))
| .del p₁ , .del p₂ => .del (compose p₁ (.del p₂))
| .del p₁ , .end => .del (compose p₁ .end)
| .ins x p₁ , .skp p₂ => .ins x (compose p₁ p₂)
| .ins x p₁ , .del p₂ => compose p₁ p₂
infixl:62 " • " => Patch.compose

def Patch.Equiv (x y : Patch a b) : Prop
  := ∀ d, x.apply d = y.apply d

instance : HasEquiv (Patch a b) where
  Equiv := Patch.Equiv

theorem compose_correct : ∀(p₁ : Patch a b) (p₂ : Patch b c) (d : List.Vector Symbol a),
     (p₁ • p₂).apply d = p₂.apply (p₁.apply d)
  := by sorry

theorem compose_assoc (p₁ : Patch a b) (p₂ : Patch b c) (p₃ : Patch c d) :
     (p₁ • p₂) • p₃ ≈ p₁ • (p₂ • p₃)
  := by sorry

structure Merge (p₁ : Patch a b)(p₂ : Patch a c) where
   size : Nat
   p₁' : Patch b size
   p₂' : Patch c size


def merge : (p₁ : Patch a b) → (p₂ : Patch a c) → Merge p₁ p₂
| .end      , .end      =>                              Merge.mk 0 .end .end
| p₁        , .ins x p₂ => let m := merge p₁ p₂;        Merge.mk m.size.succ (.ins x m.p₁') (.skp m.p₂')
| .ins x p₁ , .del p₂   => let m := merge p₁ (.del p₂); Merge.mk m.size.succ (.skp m.p₁')   (.ins x m.p₂')
| .ins x p₁ , .skp p₂   => let m := merge p₁ (.skp p₂); Merge.mk m.size.succ (.skp m.p₁')   (.ins x m.p₂')
| .ins x p₁ , .end      => let m := merge p₁ .end;      Merge.mk m.size.succ (.skp m.p₁')   (.ins x m.p₂')
| .del p₁   , .skp p₂   => let m := merge p₁ p₂;        Merge.mk m.size      m.p₁'          (.del m.p₂')
| .skp p₁   , .del p₂   => let m := merge p₁ p₂;        Merge.mk m.size      (.del m.p₁')   m.p₂'
| .del p₁   , .del p₂   => let m := merge p₁ p₂;        Merge.mk m.size      m.p₁'          m.p₂'
| .skp p₁   , .skp p₂   => let m := merge p₁ p₂;        Merge.mk m.size.succ (.skp m.p₁')   (.skp m.p₂')

theorem merge_pushout : ∀(p₁ : Patch a b)(p₂ : Patch a c),
     p₁ • (merge p₁ p₂).p₁' ≈ p₂ • (merge p₁ p₂).p₂'
  := by sorry

end Problem18
