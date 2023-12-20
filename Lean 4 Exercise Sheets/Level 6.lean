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


--(a ∣ b)

--(b ∣ a)

--(a = b)

example : ∀ (a b c : ℕ), ((0 < a) ∧ (0 < b) ∧ (0 < c)) → ((a ∣ b) ∧ (b ∣ c)) → (a ∣ c)  := by
intros a b c
intro h
cases' h with ha hbc
cases' hbc with hb hc
intro h2
cases' h2 with hab hbc
have h3 := dvd_trans hab hbc
exact h3
done


example : ∀ (a b : ℕ), ((0 < a) ∧ (0 < b)) → ((a ∣ b) ∧ (b ∣ a)) → (a = b)  := by
intros a b
intro h
cases' h with ha hb
intro h2
cases' h2 with hab hba
have h3 := dvd_antisymm hab hba
exact h3
done

--exercise 6.5
def L
  {X : Type}
  (S T : X → X → Prop)
  [IsStrictOrder X S]
  [IsStrictOrder X T]
  (p q : X × X)
  : Prop := (S p.1 q.1) ∨ ((p.1 = q.1) ∧ (T p.2 q.2))

example (S T : X → X → Prop) (hS : IsStrictTotalOrder X S) (hT : IsStrictTotalOrder X T): IsStrictTotalOrder (X × X) (L S T) := by
  haveI hLirrefl: IsIrrefl (X × X) (L S T) := { -- ¬S p p
    irrefl := by
      intro p
      intro h
      cases' h with h1 h2
      have := hS.irrefl p.1
      exact this h1
      cases' h2 with h21 h22
      have := hT.irrefl p.2
      exact this h22
      done
  }
  haveI hLtrans: IsTrans (X × X) (L S T) := { -- S p q ∧ S q r → S p r
    trans := by
      intros p q r
      intro hpq
      intro hqr
      cases' hpq with hpq1 hpq2
      cases' hqr with hqr1 hqr2
      left
      exact hS.trans p.fst q.fst r.fst hpq1 hqr1
      left
      cases' hqr2 with hqr21 hqr22
      rw [hqr21] at hpq1
      exact hpq1
      cases' hqr with hqr1 hqr2
      cases' hpq2 with hpq11 hpq12
      left
      rw [← hpq11] at hqr1
      exact hqr1
      cases' hpq2 with hpq21 hpq22
      cases' hqr2 with hqr21 hqr22
      right
      constructor
      rw [hpq21]
      exact hqr21
      exact hT.trans p.snd q.snd r.snd hpq22 hqr22
      done
  }
  haveI hLtricho : IsTrichotomous (X × X) (L S T) := { -- (S p q) ∨ (p = q) ∨ (S q p)
    trichotomous := by
      intros p q
      cases' hS.trichotomous p.fst q.fst with hS1 hS2
      cases' hT.trichotomous p.snd q.snd with hT1 hT2
      left
      constructor
      exact hS1
      left
      constructor
      exact hS1
      cases' hT.trichotomous p.snd q.snd with hT1 hT2
      cases' hS2 with hS21 hS22
      left
      right
      constructor
      exact hS21
      exact hT1
      right
      right
      left
      exact hS22
      cases' hS2 with hS21 hS22
      cases' hT2 with hT21 hT22
      right
      left
      exact Prod.ext hS21 hT21
      right
      right
      right
      constructor
      symm
      exact hS21
      exact hT22
      cases' hT2 with hT21 hT22
      right
      right
      left
      exact hS22
      right
      right
      left
      exact hS22
      done
  }
  haveI hLstrict : IsStrictOrder (X × X) (L S T) := IsStrictOrder.mk --Zusammensetzen
  exact IsStrictTotalOrder.mk   --when instances are known you can build stronger instance.
  done


--exercise 6.1
example (m n r : ℕ) : m ^(n+r) = m^n * m^r := by
induction' n with d hd
rw [Nat.zero_add]
rw [Nat.pow_zero]
rw [Nat.one_mul]
rw [succ_add]
rw [Nat.pow_succ]
rw [Nat.pow_succ]
rw [hd]
rw [mul_assoc]
rw [mul_assoc]
rw [mul_comm (m ^ r)]
done

example (m n r : ℕ) : (m^n) ^ r = m ^ (n*r) := by
induction' r with d hd
rw [Nat.mul_zero]
rw [Nat.pow_zero]
rw [Nat.pow_zero]
rw [mul_succ]
rw [Nat.pow_succ]
rw [hd]
rw [Nat.pow_add]
done

example (m n r : ℕ) : (m*n) ^ r = m ^ r * n ^ r := by
induction' r with d hd
rw [Nat.pow_zero]
rw [Nat.pow_zero]
rw [Nat.pow_zero]
rw [Nat.pow_succ]
rw [Nat.pow_succ]
rw [Nat.pow_succ]
rw [hd]
rw [mul_assoc]
rw [← mul_assoc (n ^ d) m n]
rw [mul_comm (n ^ d) m]
rw [mul_assoc]
rw [← mul_assoc]
done


--exercise 6.3
def Div_by_n
  (a b : ℕ)
  : Prop := a ∣ b


example : IsPartialOrder ℕ Div_by_n := by
  haveI isrefl : IsRefl ℕ Div_by_n := { -- a ∣ a
    refl := by
      intro a
      exact dvd_refl a
      done
  }
  haveI istrans : IsTrans ℕ Div_by_n := { -- a ∣ b ∧ b ∣ c → a ∣ c
    trans := by
      intros a b c
      intro hab
      intro hbc
      exact dvd_trans hab hbc
      done
  }
  haveI antisymm : IsAntisymm ℕ Div_by_n := { -- a ∣ b ∧ b ∣ a → a = b
    antisymm := by
      intros a b
      intro hab
      intro hba
      exact dvd_antisymm hab hba
      done
  }
  haveI ispreorder : IsPreorder ℕ Div_by_n := IsPreorder.mk --Zusammensetzen
  exact IsPartialOrder.mk
  done



--exercise 6.4
def X : Set ℕ := {1, 2, 6, 30, 210}
def Div_by_x
  (x y : X)
  : Prop := ∃z : ℕ, y = (x * z)

example : IsLinearOrder X Div_by_x := by
  haveI isrefl : IsRefl X Div_by_x := {
    refl := by
      intro x
      use 1
      rw [mul_one]
      done
  }
  haveI istrans : IsTrans X Div_by_x := {
    trans := by
      intros a b c
      intro hab
      intro hbc
      exact dvd_trans hab hbc
      done
  }
  haveI antisymm : IsAntisymm X Div_by_x := {
    antisymm := by
      intros a b
      intro hab
      intro hba
      cases' hab with z habz
      cases' hba with w hbaw
      rw [hbaw] at habz
      symm at habz
      rw [mul_assoc] at habz
      rw [Nat.mul_right_eq_self_iff] at habz
      have h2 := Nat.eq_one_of_mul_eq_one_right habz
      rw [h2] at hbaw
      rw [mul_one] at hbaw
      exact SetCoe.ext hbaw
      have h3 : (b : ℕ) ≠ 0 := by
        intro h
        simp_rw [X] at b
        cases' b with b1 b2
        simp at h
        rw [h] at b2
        repeat rw [@mem_insert_iff] at b2
        cases' b2 with b01 b02
        contradiction
        cases' b02 with b02 b06
        contradiction
        cases' b06 with b06 b30
        contradiction
        cases' b30 with b30 b210
        contradiction
        contradiction
        done
      exact Nat.pos_of_ne_zero h3
      done
  }
  haveI ispreorder : IsPreorder X Div_by_x := IsPreorder.mk
  haveI ispartialorder : IsPartialOrder X Div_by_x := IsPartialOrder.mk --Zusammensetzen zu PartialOrder
  haveI istotal : IsTotal X Div_by_x := sorry --do this on paper --have 1 ∣ 1 for all division
  exact IsLinearOrder.mk --Zusammensetzen zu LinearOrder
  done


--alternative

def X' : Set ℕ := {1, 2, 6, 30, 210}
def Div_by_x'
  (x y : X')
  : Prop := x.val ∣ y.val
