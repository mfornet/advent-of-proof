import Mathlib.Tactic
-- I will not take (many) style points for using Classical.Choice here.  It's very hard to avoid in Lean.

namespace Problem9

structure Queue (A : Type) : Type where
    size_front  : Nat
    size_back   : Nat
    front : List A
    back  : List A

    invariant : size_back ≤ size_front
    size_inv₁ : List.length front = size_front
    size_inv₂ : List.length back = size_back

structure CorrectQueue (Q : Type → Type) : Type 2 where
    abstraction : Q A → List A
    enqueue     : A → Q A → Q A
    dequeue     : Q A → Option (Q A)
    first       : Q A → Option A
    size        : Q A → Nat
    empty       : Q A

    emptyᵣ      : abstraction empty = ([] : List A)
    sizeᵣ       : ∀ (q : Q A), size q = List.length (abstraction q)
    firstᵣ      : ∀ (q : Q A), first q = List.head? (abstraction q)
    dequeueᵣ    : ∀ (q : Q A), Option.map abstraction (dequeue q) = List.tail? (abstraction q)
    enqueueᵣ    : ∀ (q : Q A) x, abstraction (enqueue x q) = abstraction q ++ [x]

def enqueueQ  (x : A)(q : Queue A) : Queue A := dite (Nat.succ q.size_back ≤ q.size_front)
    (λ p => Queue.mk q.size_front (Nat.succ q.size_back) q.front (x :: q.back)
            p q.size_inv₁ (by simp [q.size_inv₂]))
    (λ p => Queue.mk (q.size_front + Nat.succ (q.size_back)) 0 (q.front ++ List.reverse (x :: q.back)) []
            (by linarith) (by simp [q.size_inv₁, q.size_inv₂]) (by simp))

def dequeueQ  (q : Queue A) : Option (Queue A) := match q.front with
   | []        => .none
   | (x :: xs) => .some (dite (q.size_back ≤ q.size_front - 1)
                           (λ p => Queue.mk (q.size_front - 1) q.size_back (List.tail q.front) q.back
                                     p (by simp [q.size_inv₁]) q.size_inv₂)
                           (λ p => Queue.mk (q.size_front - 1 + q.size_back) 0 (List.tail q.front ++ List.reverse q.back) []
                                     (by linarith) (by simp [q.size_inv₁, q.size_inv₂]) (by simp)))

def firstQ (q : Queue A) : Option A :=  match q.front with
   | []        => .none
   | (x :: _)  => .some x

def sizeQ ( q : Queue A) : Nat := q.size_front + q.size_back

def emptyQ : Queue A := Queue.mk 0 0 [] [] (by linarith) (by trivial) (by trivial)

def goal : CorrectQueue Queue := by sorry

end Problem9
