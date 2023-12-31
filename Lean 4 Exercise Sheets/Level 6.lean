import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Basic

open Set --I open all these features so that I can use the functions without the prefix e.g. I can write Icc instead of Set.Icc
open Function
open Real
open Nat


--Def. Weak order: WO1 - a R b and b R c imply a R c
--                 WO2 - either a R b or b R a (or both)
--                 WO3 - a R b and b R a imply a = b

--Def. Partial order: WO1 - a R b and b R c imply a R c
--                    WO3 - a R b and b R a imply a = b

--Def. Strict order: SO1 - a S b and b S c imply a S c
--                   SO2 - precisely one of the following hold (and not the other two)
--                         a S b, b S a, a = b


example : ∀ (a b c : ℕ), ((0 < a) ∧ (0 < b) ∧ (0 < c)) → ((a ∣ b) ∧ (b ∣ c)) → (a ∣ c)  := by --try to prove transitivity.
sorry
done


example : ∀ (a b : ℕ), ((0 < a) ∧ (0 < b)) → ((a ∣ b) ∧ (b ∣ a)) → (a = b)  := by --try to prove antisymmertry.
sorry
done


--Exercises from exercise sheet 6---------------------------------------------------------

--exercise 6.1 (Multiplication and Powers on ℕ)
example (m n r : ℕ) : m ^(n+r) = m^n * m^r := by --This are similar to exercise 4 in level 5.
sorry
done


example (m n r : ℕ) : (m^n) ^ r = m ^ (n*r) := by
sorry
done


example (m n r : ℕ) : (m*n) ^ r = m ^ r * n ^ r := by
sorry
done



--exercise 6.3
def Div_by_n
  (a b : ℕ)
  : Prop := a ∣ b


example : IsPartialOrder ℕ Div_by_n := by --I have given you all the instances you need for a partial order. Prove all of them, then "exact IsPartialOrder.mk" will finish the proof.
haveI isrefl : IsRefl ℕ Div_by_n := { -- a ∣ a
  refl := by
    sorry
    done
}
haveI istrans : IsTrans ℕ Div_by_n := { -- a ∣ b ∧ b ∣ c → a ∣ c
  trans := by
    sorry
    done
}
haveI antisymm : IsAntisymm ℕ Div_by_n := { -- a ∣ b ∧ b ∣ a → a = b
  antisymm := by
    sorry
    done
}
haveI ispreorder : IsPreorder ℕ Div_by_n := IsPreorder.mk --Put together the instances isrefl and istrans you have proved.
exact IsPartialOrder.mk --Partial order is made up from isantisymm and ispreorder.
done



--exercise 6.4
def X : Set ℕ := {1, 2, 6, 30, 210}
def Div_by_x
  (x y : X)
  : Prop := ∃z : ℕ, y = (x * z)

example : IsLinearOrder X Div_by_x := by --Do the same as before but for a linear order (Lean's name for weak order).
haveI isrefl : IsRefl X Div_by_x := {
  refl := by
    sorry
    done
}
haveI istrans : IsTrans X Div_by_x := {
  trans := by
    sorry
    done
}
haveI antisymm : IsAntisymm X Div_by_x := {
  antisymm := by
    sorry
    done
}
haveI ispreorder : IsPreorder X Div_by_x := IsPreorder.mk
haveI ispartialorder : IsPartialOrder X Div_by_x := IsPartialOrder.mk --Putting together PartialOrder.
haveI istotal : IsTotal X Div_by_x := {
  total := by --I would not do this prove if I were you. It is almost 100 lines of just different cases.
    sorry
    done
}
exact IsLinearOrder.mk --Putting together LinearOrder.
done



--exercise 6.5
def L
  {X : Type}
  (S T : X → X → Prop)
  [IsStrictOrder X S]
  [IsStrictOrder X T]
  (p q : X × X)
  : Prop := (S p.1 q.1) ∨ ((p.1 = q.1) ∧ (T p.2 q.2))


example (S T : X → X → Prop) (hS : IsStrictTotalOrder X S) (hT : IsStrictTotalOrder X T): IsStrictTotalOrder (X × X) (L S T) := by --This one is tricky, but maybe you have enough practice by now to do this. Otherwise have a look at the solution and try it another time.
haveI hLirrefl: IsIrrefl (X × X) (L S T) := { -- ¬S p p
  irrefl := by
    sorry
    done
}
haveI hLtrans: IsTrans (X × X) (L S T) := { -- S p q ∧ S q r → S p r
  trans := by
    sorry
    done
}
haveI hLtricho : IsTrichotomous (X × X) (L S T) := { -- (S p q) ∨ (p = q) ∨ (S q p)
  trichotomous := by
    sorry
    done
}
haveI hLstrict : IsStrictOrder (X × X) (L S T) := IsStrictOrder.mk --Putting together StrictOrder.
exact IsStrictTotalOrder.mk   --Putting together StrictTotalOrder.
done
done
