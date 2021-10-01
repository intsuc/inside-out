import InsideOut.Elaborate

notation Γ " | " Ψ " ⊢ " e => inferOutsideIn Γ Ψ e

#eval IO.println "-- ok"

#eval [] | [] ⊢ exp ff

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ≔ abs "x" ⇒ #"x";
  abs "x" ⇒ #"f" ◁ #"x"

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ #"f" ◁ #"x"

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"y";
  abs "x" ⇒ #"f" ◁ #"x"

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ abs "y" ⇒ #"f" ◁ #"x" ◁ #"y"

#eval [] | [] ⊢ exp (abs "x" ⇒ #"x") ◁ ff

#eval [] | [] ⊢ exp (abs "x" ⇒ ff) ◁ ff

#eval [] | [] ⊢ exp (iff ff then abs "x" ⇒ #"x" else abs "x" ⇒ #"x") ◁ ff

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  (abs "x" ⇒ #"f") ◁ ff

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  (abs "x" ⇒ abs "y" ⇒ #"f") ◁ ff ◁ ff

#eval IO.println "-- error"

#eval [] | [] ⊢ exp #"x"

#eval [] | [] ⊢ exp iff abs "x" ⇒ #"x" then ff else ff

#eval [] | [] ⊢ exp abs "x" ⇒ #"x"

#eval [] | [] ⊢ exp abs "x" ⇒ ff

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ #"f" ◁ ff

#eval [] | [] ⊢ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ abs "y" ⇒ #"f" ◁ #"x" ◁ #"x"
