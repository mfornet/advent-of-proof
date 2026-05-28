import Mathlib.Tactic

class CorrectQueue {A: Type} (Q : Type) where
    abstraction : Q → List A
    enqueue     : A → Q → Q
    -- dequeue     : Q A → Option (Q A)
    -- first       : Q A → Option A
    size        : Q → Nat
    empty       : Q

    -- emptyᵣ      : abstraction empty = ([] : List A)
    -- sizeᵣ       : ∀ (q : Q A), size q = List.length (abstraction q)
    -- firstᵣ      : ∀ (q : Q A), first q = List.head? (abstraction q)
    -- dequeueᵣ    : ∀ (q : Q A), Option.map abstraction (dequeue q) = List.tail? (abstraction q)
    -- enqueueᵣ    : ∀ (q : Q A) x, abstraction (enqueue x q) = abstraction q ++ [x]

structure Queue (A : Type) : Type where
    size_front  : Nat
    size_back   : Nat
    front : List A
    back  : List A

    invariant : size_back ≤ size_front
    size_inv₁ : List.length front = size_front
    size_inv₂ : List.length back = size_back

def Queue.empty : Queue A := {
  size_front := 0
  size_back := 0
  front := []
  back := []
  invariant := by simp
  size_inv₁ := by simp
  size_inv₂ := by simp
}

instance {A : Type} : @CorrectQueue A (Queue A) where
    abstraction q := q.front ++ q.back.reverse
    enqueue x q := {
      q with
        back := x :: q.back
        size_back := q.size_back + 1
        invariant := by sorry
        size_inv₂ := by simp [List.length]; exact q.size_inv₂
    }
    size q := q.size_front + q.size_back
    empty := Queue.empty
