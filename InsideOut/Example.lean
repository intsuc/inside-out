import InsideOut.Elaborate

#eval IO.println "-- ok"

#eval inferOutsideIn #[] $ exp ff

#eval inferOutsideIn #[] $ exp
  let "f" ∷ bool ⇒ bool ≔ abs "x" ⇒ #"x";
  abs "x" ⇒ #"f" ◁ #"x"

#eval inferOutsideIn #[] $ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ #"f" ◁ #"x"

#eval inferOutsideIn #[] $ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"y";
  abs "x" ⇒ #"f" ◁ #"x"

#eval inferOutsideIn #[] $ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ abs "y" ⇒ #"f" ◁ #"x" ◁ #"y"



#eval IO.println "-- error"

#eval inferOutsideIn #[] $ exp abs "x" ⇒ #"x"

#eval inferOutsideIn #[] $ exp abs "x" ⇒ ff

#eval inferOutsideIn #[] $ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ #"f" ◁ ff

#eval inferOutsideIn #[] $ exp
  let "f" ∷ bool ⇒ bool ⇒ bool ≔ abs "x" ⇒ abs "y" ⇒ #"x";
  abs "x" ⇒ abs "y" ⇒ #"f" ◁ #"x" ◁ #"x"
