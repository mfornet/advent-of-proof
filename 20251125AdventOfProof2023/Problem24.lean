import Mathlib.Tactic

-- Mathlib already has something called Tree
inductive Tree' : Type where
| leaf : Tree'
| branch : Tree' → Tree' → Tree'
deriving Repr

def toList (d : Nat) : Tree' → List Nat
| .leaf => [d]
| .branch t₁ t₂ => toList d.succ t₁ ++ toList d.succ t₂

structure StackItem where
  tree : Tree'
  depth : Nat

def StackItem.new (d : Nat) : StackItem :=
  { tree := .leaf, depth := d }

def StackItem.merge (i j : StackItem) (_ : i.depth = j.depth): StackItem :=
  { tree := .branch i.tree j.tree, depth := i.depth.pred }

def Stack_push (i : StackItem) : List StackItem → List StackItem
  | [] => [i]
  | j :: js =>
    if h : j.depth = i.depth then
      Stack_push (j.merge i h) js
    else
      i :: j :: js

def depth (stack : List StackItem) : Nat :=
  stack.head?.map (·.depth) |>.getD 0

lemma Stack_push_non_merge (stack : List StackItem) (i : StackItem) (h : depth stack < i.depth) : Stack_push i stack = i :: stack := by
  cases stack with
  | nil => simp [Stack_push]
  | cons j js =>
    simp [Stack_push]
    intro he
    simp [depth] at h
    linarith

lemma Stack_push_depth_mon : depth (Stack_push i stack) ≤ i.depth := by
  induction' stack generalizing i
  case nil => simp [Stack_push, depth]
  case cons j js h =>
    if h1 : j.depth = i.depth then
      simp [Stack_push, h1]
      specialize @h (j.merge i h1)
      suffices (j.merge i h1).depth ≤ i.depth by linarith
      simp [StackItem.merge]
      linarith
    else
      simp [Stack_push, depth, h1]

def toTreeRec (stack : List StackItem) : List Nat → List Tree'
  | [] => stack.map (·.tree)
  | d :: ds => toTreeRec (Stack_push (StackItem.new d) stack) ds

lemma toTreeRec_main (stack : List StackItem) (h : depth stack ≤ d) :
  toTreeRec stack (toList d t ++ suff) = toTreeRec (Stack_push { depth := d, tree := t } stack) suff := by
  induction' t generalizing d suff stack
  case leaf => simp [toList, toTreeRec, StackItem.new]
  case branch t₁ t₂ ih₁ ih₂ =>
    simp [toList]
    rw [@ih₁ (d + 1) _ _ (by linarith)]
    rw [@ih₂ (d + 1) _ _ (by grind [Stack_push_depth_mon])]

    suffices (Stack_push { tree := t₂, depth := d + 1 } (Stack_push { tree := t₁, depth := d + 1 } stack)) = (Stack_push { tree := t₁.branch t₂, depth := d } stack) by grind
    rw [Stack_push_non_merge stack _ (by grind)]
    simp [Stack_push, StackItem.merge]

lemma toTreeRec_merge (suff : List Nat): toTreeRec [ { tree := t₁, depth := d + 1 }] (toList (d + 1) t₂ ++ suff) = toTreeRec [ { tree := .branch t₁ t₂, depth := d }] suff := by
  rw [toTreeRec_main _ (by simp [depth])]
  simp [Stack_push, StackItem.merge]

lemma toTreeRec_cons :
  toTreeRec [] (toList n t ++ suff) = toTreeRec [ { tree := t, depth := n }] suff
  := by
  rw [toTreeRec_main _ (by simp [depth])]
  simp [Stack_push]

lemma toTreeRec_merge_empty_suff : toTreeRec [ { tree := t₁, depth := d + 1 }] (toList (d + 1) t₂) = toTreeRec [ { tree := .branch t₁ t₂, depth := d }] [] := by
  have h := @toTreeRec_merge t₁ d t₂ []
  simp only [List.append_nil] at h
  assumption

def toTree (l : List Nat) : Option Tree' :=
  toTreeRec [] l |>.head?

def toTree_inv_of_toList : ∀ (n : Nat) (t : Tree'), toTree (toList n t) = some t := by
  intro n t
  induction' t generalizing n
  case leaf => simp [toList, toTree, toTreeRec, StackItem.new, Stack_push]
  case branch t₁ t₂ ih₁ ih₂ =>
    simp [toList]
    specialize ih₁ (n + 1)
    specialize ih₂ (n + 1)
    simp [toTree]
    rw [toTreeRec_cons, toTreeRec_merge_empty_suff]
    simp [toTreeRec]

theorem toList_injective : toList n t = toList n t' → t = t' := by
  intro h
  suffices some t = some t' by grind
  rw [← toTree_inv_of_toList n t, ← toTree_inv_of_toList n t', h]
