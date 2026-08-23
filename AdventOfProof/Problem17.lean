namespace Problem17

variable {Act : Type}

inductive Process (Act : Type) : Type where
| act   : Act → Process Act
| skip  : Process Act
| abort : Process Act
| seq   : Process Act → Process Act → Process Act
| cho   : Process Act → Process Act → Process Act
| par   : Process Act → Process Act → Process Act

infixr:70 " ; "=>Process.seq
infixr:60 " ‖ "=>Process.par
notation "⟨" x "⟩" => Process.act x
instance : HAdd (Process Act) (Process Act) (Process Act) where
  hAdd := Process.cho

def NoPar : Process Act → Prop
| ⟨ _ ⟩ => True
| .abort => True
| .skip  => True
| P ; Q => NoPar P ∧ NoPar Q
| P + Q => NoPar P ∧ NoPar Q
| _ ‖ _ => False

def interleave : List Act → List Act → List (List Act)
| [] , xs => [ xs ]
| xs , [] => [ xs ]
| x :: xs, y :: ys => List.map (List.cons x) (interleave xs (y :: ys))
                   ++ List.map (List.cons y) (interleave (x :: xs) ys)


def Process.semantics : Process Act → List (List Act)
| ⟨ x ⟩ => [ [ x ] ]
| .abort => []
| .skip  => [ [] ]
| P + Q => P.semantics ++ Q.semantics
| P ; Q => P.semantics.flatMap (fun p => Q.semantics.map (List.append p))
| P ‖ Q => P.semantics.flatMap (fun p => Q.semantics.flatMap (interleave p))
notation "⟦" x "⟧" => Process.semantics x

def Process.equiv (P Q : Process Act) : Prop := ∀xs, xs ∈ ⟦ P ⟧ ↔ xs ∈ ⟦ Q ⟧
instance : HasEquiv (Process Act) where
  Equiv := Process.equiv

theorem goal : ∀ (P : Process Act), ∃ P', P' ≈ P ∧ NoPar P' := by sorry

end Problem17
