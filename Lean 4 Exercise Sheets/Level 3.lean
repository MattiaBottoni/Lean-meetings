import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-This sheet was mainly about natural and strong induction. Before the exercises from sheet 3, you find some
simple exercises where induction is used.-/

variable (n : ℕ)

open Nat --I open all these features so that I can use the functions without the prefix e.g. I can write add_succ instead of Nat.add_succ
open BigOperators
open Finset


example : 0 + n = n := by --try it yourself
sorry
done


example : n + m = m + n := by --try it yourself
sorry
done


example : ∑ k in Finset.Ico 1 (n+1), (2*k-1) = n^2 := by --try it yourself
sorry
done


example : ∑ i in range (n+1), (i:ℚ) = (n:ℚ)*(n+1)/(2 : ℚ) := by --try it yourself, this is a bit difficult
sorry
done


--Exercises from exercise sheet 3---------------------------------------------------------

theorem two_dvd_n_succ_n : 2 ∣ n * n + n := by --this is used in two exercises. If you want to prove this by yourself, delete the proof.
rw [← mul_add_one]
by_cases h : Even (n)
rw [even_iff_two_dvd] at h
exact Dvd.dvd.mul_right h (n + 1)
have h2 : Even (n+1)
rw [Nat.even_add_one] --Note that here you still need to write the prefix Nat. sometimes you have to still do this.
exact h
rw [even_iff_two_dvd] at h2
exact Dvd.dvd.mul_left h2 n
done


--exercise 3.1
example : (∑ k in range (n+1), k)^2 = ∑ k in range (n+1), k^3 := by --You will have to use "rw [sum_range_one]" and "rw [sum_range_succ]" here. Also, at some point you will want to use Gauss's Formula, for that you need "rw [sum_range_id]"
sorry
done



--exercise 3.2
example : 6 ∣ (n^3 - n) := by --It is actually easier to solve this exercise with natural induction. Here you sometimes will have to write "Nat." before a tactic.
sorry
done


theorem two_lt_n_cubed_sub_n (h : 2 < n) : 2 < n^3 - n := by --this is needed for the proof with strong induction. If you want to prove this by yourself, delete the proof.
have h1 : n^3 - n = n * (n+1) * (n-1)
rw [pow_three]
rw [mul_assoc]
rw [← sq_sub_sq n 1]
ring_nf
rw [Nat.mul_sub_left_distrib]
rw [mul_one]
rw [pow_three]
rw [pow_two]
rw [h1]
have h3 : 1 < (n+1) * (n-1)
have h3a : 1 < n+1
linarith
have h3b : 1 < n - 1
rw [lt_tsub_iff_left]
linarith
exact lt_mul_of_one_lt_of_lt' h3a h3b
rw [mul_assoc]
rw [mul_comm]
exact lt_mul_of_one_lt_of_lt' h3 h
done


example : 6 ∣ (n^3 - n) := by --With strong induction. This one of the first exercises I marked red. I spent hours finding the correct proof and I had to define the theorem above to solve it.
induction' n using Nat.twoStepInduction with d hd hd2 --as you will see,we don't use hd2 in the whole proof, which shows, that we could have done it with classical induction.
sorry
sorry
sorry
done



--exercise 3.3
example (k : ℕ) : (x + y) ^ n = ∑ k in range (n + 1), x^(n - k) * y^k * Nat.choose n k := by --I really don't recommend you to do this exercise in Lean. The proof has very long notations and therefore gets ugly. I have not finished the whole proof up to this date.
sorry
done



--exercise 3.4.1
def R (x y : ℤ) : Prop := |x-y| < 1


example : R 1 1 := by --this is just to get you used to the notation.
rw [R]
rw [sub_self]
rw [abs_zero]
linarith
done


theorem R_is_reflexive : Reflexive R := by --These should not give you a hard time.
sorry
done

example : ∀x : ℤ,  |x-x| < 1 := by --I also wrote the exercises if you would not define R in the beginning.
sorry
done


theorem R_is_symmetric : Symmetric R := by
sorry
done

example : ∀ x y : ℤ, |x - y|  < 1 → |y-x| < 1 := by
sorry
done


theorem R_is_transitive : Transitive R := by
sorry
done

example : ∀ x y z : ℤ, (|x-y| < 1 ∧ |y-z| < 1) → |x-z| < 1 := by
sorry
done


--exercise 3.4.2
def R_le (x y : ℤ) : Prop := |x-y| ≤ 1


theorem R_le_is_reflexive : Reflexive R_le := by
sorry
done

example : ∀x : ℤ, |x-x| ≤ 1 := by
sorry
done


theorem R_le_is_symmetric : Symmetric R_le := by
sorry
done

example : ∀ x y : ℤ, |x-y| ≤ 1 → |y-x| ≤ 1 := by
sorry
done


theorem R_le_is_not_transitive : ¬Transitive R_le := by --This one gave me a headache for some time, because we have a ¬ in the hypothesis. Have a look at the solutions or try it yourself.
sorry
done

example : ∃ x y z : ℤ,  |x-y| ≤ 1 ∧ |y-z| ≤ 1 ∧ |x-z| > 1 := by
sorry
done



--exercise 3.5
section
variable
  {X : Sort _}
  (x y a : X)
  (R : X → X → Prop)
open Set


def emptyR (_ _ : Type) : Prop := False


theorem emptyR_is_symmetric : Symmetric emptyR := by --It may be a bit difficult to understand how I defined emptyR. But if you consider it as given, the proofs aren't that hard.
sorry
done


theorem emptyR_is_transitive : Transitive emptyR := by
sorry
done


theorem emptyR_is_not_reflexive : ¬Reflexive emptyR := by
sorry
done



--exercise 3.6.1
theorem R_is_reflexiv_iff (h_sym : Symmetric R) (h_trans : Transitive R) (h_a : ∀ x : X, R a x) : Reflexive R := by --after "rw [Reflexive]", you will have to use "have h2 : ∀ x : X, R x a" and for the last step of the proof, you should use "exact h_trans (h2 x) (h_a x)".
sorry
done


--exercise 3.6.2
theorem R_is_not_reflexiv_without_h_a : ∃ R: Type → Type → Prop, Symmetric R ∧  Transitive R ∧  ¬Reflexive R := by --Start this proof with "use emptyR" and then use the theorems from exercise 5 by typing "exact NameOfTheTheorem"
use emptyR
sorry
done
