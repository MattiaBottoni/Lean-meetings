import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-This sheet was mainly about natural and strong induction. Before the exercises from sheet 3, you find some
simple exercies where induction is used.-/

variable (n : ℕ)

open Nat --I open all these features so that I can use the functions without the prefix e.g. I can write add_succ instead of Nat.add_succ
open BigOperators
open Finset


example : 0 + n = n := by --try it yourself
induction' n with k hk
simp
rw [add_succ]
rw [hk]
done


example : 0 + n = n := by --solution
induction' n with d hd
rw [Nat.add_zero] --here we still need to write Nat.add_zero, as Lean needs to know which zero (ℕ or ℝ) we are using.
rw [add_succ]
rw [hd]
done


example : n + m = m + n := by --try it yourself
induction' n with k hk
rw [Nat.add_zero]
rw [Nat.zero_add]
rw [succ_add]
rw [add_succ]
rw [hk]
done


example : n + m = m + n := by --solution
induction' n with d hd
rw [Nat.add_zero]
rw [Nat.zero_add]
rw [Nat.add_succ]
rw [Nat.succ_add]
rw [hd]
done


example : ∑ k in Finset.Ico 1 (n+1), (2*k-1) = n^2 := by --try it yourself
induction' n with d hd
simp
rw [sum_Ico_succ_top]
rw [hd]
rw [succ_eq_add_one]
ring_nf
rw [add_comm]
rw [add_left_inj]
rw [add_comm]
conv_rhs => rw [add_comm]
linarith
done


example : ∑ k in Finset.Ico 1 (n+1), (2*k-1) = n^2 := by --solution
induction' n with d hd
simp
rw [succ_eq_add_one]
rw [sum_Ico_succ_top]
rw [add_comm]
rw [hd]
ring_nf
rw [add_comm 2]
rw [Nat.add_sub_assoc]
rw [add_comm]
rw [add_left_inj]
rw [add_comm]
rw [add_left_inj]
norm_num
linarith
linarith
done


example : ∑ i in range (n+1), (i:ℚ) = (n:ℚ)*(n+1)/(2 : ℚ) := by --try it yourself, this is a bit difficult
induction' n with k hk
rw [sum_range_one]
simp
rw [sum_range_succ]
rw [hk]
rw [succ_eq_add_one]
ring_nf
rw [add_assoc]
push_cast
ring_nf
done


--Exercises from exercise sheet 3---------------------------------------------------------

theorem two_dvd_n_succ_n : 2 ∣ n * n + n := by --this is used in two exercises
rw [← mul_add_one]
by_cases h : Even (n)
rw [even_iff_two_dvd] at h
exact Dvd.dvd.mul_right h (n + 1)
have h2 : Even (n+1)
rw [Nat.even_add_one]
exact h
rw [even_iff_two_dvd] at h2
exact Dvd.dvd.mul_left h2 n
done


--exercise 3.1
example : (∑ k in range (n+1), k)^2 = ∑ k in range (n+1), k^3 := by
induction' n with d hd
rw [sum_range_one]
rw [sum_range_one]
simp
rw [sum_range_succ]
rw [add_sq]
rw [hd]
rw [succ_eq_add_one]
conv_rhs => rw [sum_range_succ]
rw [add_assoc]
rw [add_left_cancel_iff]
rw [sum_range_id] --Gauss summation formula!
ring_nf
simp
rw [Nat.div_mul_cancel]
rw [mul_assoc]
rw [Nat.div_mul_cancel]
ring
exact two_dvd_n_succ_n d
exact two_dvd_n_succ_n d
done



--exercise 3.2
example : 6 ∣ (n^3 - n) := by
induction' n with d hd
rw [pow_three]
rw [Nat.zero_mul]
rw [Nat.sub_zero]
exact dvd_zero 6
rw [succ_eq_add_one]
ring_nf
rw [← Nat.sub_sub]
rw [add_assoc]
rw [add_assoc]
rw [Nat.add_sub_self_left]
rw [← add_assoc]
rw [Nat.add_sub_assoc]
rw [← Nat.dvd_add_iff_left hd]
rw [← add_mul]
rw [pow_two]
rw [← mul_one_add]
have h2 : 6 = 2 * 3
norm_num
rw [h2]
apply mul_dvd_mul_right
rw [add_comm]
exact two_dvd_n_succ_n d
apply Nat.le_self_pow
norm_num
done


theorem two_lt_n_cubed_sub_n (h : 2 < n) : 2 < n^3 - n := by
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


example : 6 ∣ (n^3 - n) := by --with strong induction
 induction' n using Nat.twoStepInduction with d hd hd2 --we don't use hd2 in the whole proof, which shows, that we could have done it with classical induction.
 simp
 simp
 by_cases hd1 : 2 ≤ d
 rw [succ_eq_add_one]
 rw [add_assoc]
 rw [one_add_one_eq_two]
 ring_nf
 rw [add_comm 2 d]
 rw [Nat.add_sub_assoc]
 rw [← Nat.sub_sub]
 rw [← Nat.add_sub_assoc]
 rw [add_comm]
 rw [Nat.add_sub_assoc]
 rw [← Nat.dvd_add_iff_right hd]
 have h1 : 8 - 2 = 6
 norm_num
 rw [add_comm]
 rw [add_comm 8 (d * 12)]
 rw [← add_assoc]
 rw [Nat.add_sub_assoc]
 rw [h1]
 have h2 : 12 = 2 * 6
 norm_num
 rw [h2]
 rw [← mul_assoc]
 rw [← add_mul]
 rw [Nat.dvd_add_self_right]
 apply dvd_mul_left
 norm_num
 nlinarith
 rw [le_iff_eq_or_lt] at hd1
 rw [le_iff_eq_or_lt]
 cases' hd1 with hde hdg
  right
 rw [← hde]
 norm_num
 right
 exact two_lt_n_cubed_sub_n d hdg
 rw [le_iff_eq_or_lt] at hd1
 rw [le_iff_eq_or_lt]
 cases' hd1 with hde hdg
 right
 rw [← hde]
 norm_num
 right
 rw [add_comm]
 apply Nat.add_lt_of_lt_sub
 exact two_lt_n_cubed_sub_n d hdg
 rw [not_le] at hd1
 have h1 : d = 0 ∨ d = 1
 rw [← le_one_iff_eq_zero_or_eq_one]
 linarith
 cases' h1 with h0 h1
 rw [h0]
 norm_num
 rw [h1]
 norm_num
 done



--exercise 3.3
example (k : ℕ) : (x + y) ^ n = ∑ k in range (n + 1), x^(n - k) * y^k * Nat.choose n k := by
induction' n with d hd
simp
rw [succ_eq_add_one]
rw [pow_add]
rw [hd]
rw [pow_one]
rw [mul_add]
have h2 : (∑ k in range (d + 1), x ^ (d - k) * y ^ k * Nat.choose d k) * y = (∑ x_1 in range d, x ^ (d - x_1) * y ^ x_1 * Nat.choose d x_1 + x ^ (d - d) * y ^ d * Nat.choose d d) * y
rw [sum_range_succ]
rw [h2]
rw [Nat.choose_self]
rw [mul_one]
rw [add_comm]
rw [add_mul]
rw [Nat.sub_self]
rw [Nat.pow_zero]
rw [one_mul]
rw [← pow_one y]
rw [← pow_mul]
rw [one_mul]
rw [← pow_add]
rw [pow_one]
rw [sum_range_succ']
rw [Nat.choose_zero_right]
rw [Nat.pow_zero]
rw [mul_one]
rw [mul_one]
rw [add_mul]
rw [Nat.sub_zero]
rw [← pow_one x]
rw [← pow_mul]
rw [one_mul]
rw [← pow_add]
rw [pow_one]
have h3 : (∑ x_1 in range d, x ^ (d - x_1) * y ^ x_1 * Nat.choose d x_1) * y = (∑ x_1 in range d, x ^ (d - x_1) * y ^ (x_1 + 1) * Nat.choose d x_1)
sorry
rw [h3]
have h4 : (∑ k in range d, x ^ (d - (k + 1)) * y ^ (k + 1) * Nat.choose d (k + 1)) * x = (∑ k in range d, x ^ (d - k) * y ^ (k + 1) * Nat.choose d (k + 1))
sorry
rw [h4]
rw [add_assoc]
rw [add_comm (∑ k in range d, x ^ (d - k) * y ^ (k + 1) * Nat.choose d (k + 1))  (x ^ (d + 1))]
rw [add_comm]
rw [← add_assoc]
have h5 : ∑ k in range d, x ^ (d - k) * y ^ (k + 1) * Nat.choose d (k + 1) +
    ∑ x_1 in range d, x ^ (d - x_1) * y ^ (x_1 + 1) * Nat.choose d x_1 = ∑ k in range d, x ^ (d - k) * y ^ (k + 1) * (Nat.choose d (k + 1) + Nat.choose d k)
sorry
rw [add_assoc]
rw [h5]
sorry
done



--exercise 3.4.1
def R (x y : ℤ) : Prop := |x-y| < 1


example : R 1 1 := by
rw [R]
rw [sub_self]
rw [abs_zero]
linarith
done


theorem R_is_reflexive : Reflexive R := by
rw [Reflexive]
intro x
rw [R]
rw [sub_self]
rw [abs_zero]
linarith
done

example : ∀x : ℤ,  |x-x| < 1 := by
intro x
rw [sub_self]
rw [abs_zero]
linarith
done


theorem R_is_symmetric : Symmetric R := by
rw [Symmetric]
intros x y
intro h
rw [R]
rw [R] at h
rw [abs_sub_comm]
exact h
done

example : ∀ x y : ℤ, |x - y|  < 1 → |y-x| < 1 := by
intro x
intro y
intro h
rw [abs_sub_comm]
exact h
done


theorem R_is_transitive : Transitive R := by
rw [Transitive]
intro x
intro y
intro z
intro hxy
intro hyz
rw [R] at hxy
rw [R] at hyz
rw [R]
rw [← add_zero x]
rw [← sub_self y]
rw [← add_comm_sub]
rw [← add_sub]
rw [Int.abs_lt_one_iff] at hxy
rw [Int.abs_lt_one_iff] at hyz
rw [hxy]
rw [hyz]
rw [add_zero]
rw [abs_zero]
linarith
done

example : ∀ x y z : ℤ, (|x-y| < 1 ∧ |y-z| < 1) → |x-z| < 1 := by
intro x
intro y
intro z
intro h
rw [← add_zero x]
rw [← sub_self y]
rw [← add_comm_sub]
rw [← add_sub]
cases' h with hxy hyz
rw [Int.abs_lt_one_iff] at hxy
rw [Int.abs_lt_one_iff] at hyz
rw [hxy]
rw [hyz]
rw [add_zero]
rw [abs_zero]
linarith
done


--exercise 3.4.2
def R_le (x y : ℤ) : Prop := |x-y| ≤ 1


theorem R_le_is_reflexive : Reflexive R_le := by
rw [Reflexive]
intro x
rw [R_le]
rw [sub_self]
rw [abs_zero]
linarith
done

example : ∀x : ℤ, |x-x| ≤ 1 := by
intro x
rw [sub_self]
rw [abs_zero]
linarith
done


theorem R_le_is_symmetric : Symmetric R_le := by
rw [Symmetric]
intros x y
intro h
rw [R_le] at h
rw [R_le]
rw [abs_sub_comm]
exact h
done

example : ∀ x y : ℤ, |x-y| ≤ 1 → |y-x| ≤ 1 := by
intro x
intro y
intro h
rw [abs_sub_comm]
exact h
done


theorem R_le_is_not_transitive : ¬Transitive R_le := by
rw [Transitive]
intro h
have h1 : R_le 0 1
rw [R_le]
norm_num
have h2 : R_le 1 2
rw [R_le]
norm_num
have h3 : R_le 0 2
exact h h1 h2
rw [R_le] at h3
rw [zero_sub] at h3
rw [abs_neg] at h3
rw [abs_two] at h3
norm_num at h3
done

example : ∃ x y z : ℤ,  |x-y| ≤ 1 ∧ |y-z| ≤ 1 ∧ |x-z| > 1 := by
use 2
use 1
use 0
constructor
norm_num
constructor
norm_num
norm_num
done



--exercise 3.5
section
variable
  {X : Sort _}
  (x y a : X)
  (R : X → X → Prop)
open Set


def emptyR (_ _ : Type) : Prop := False


theorem emptyR_is_symmetric : Symmetric emptyR := by
rw [Symmetric]
intro x
intro y
intro h
rw [emptyR] at h
exfalso
exact h
done


theorem emptyR_is_transitive : Transitive emptyR := by
rw [Transitive]
intro x
intro y
intro z
intro hxy
intro hyz
rw [emptyR] at hxy
exfalso
exact hxy
done


theorem emptyR_is_not_reflexive : ¬Reflexive emptyR := by
intro h
rw [Reflexive] at h
specialize h X
rw [emptyR] at h
exact h
done



--exercise 3.6.1
theorem R_is_reflexiv_iff (h_sym : Symmetric R) (h_trans : Transitive R) (h_a : ∀ x : X, R a x) : Reflexive R := by
rw [Reflexive]
have h2 : ∀ x : X, R x a
rw [Symmetric] at h_sym
intro x
exact h_sym (h_a x)
rw [Transitive] at h_trans
intro x
exact h_trans (h2 x) (h_a x)
done


--exercise 3.6.2
theorem R_is_not_reflexiv_without_h_a : ∃ R: Type → Type → Prop, Symmetric R ∧  Transitive R ∧  ¬Reflexive R := by
use emptyR
constructor
exact emptyR_is_symmetric
constructor
exact emptyR_is_transitive
apply emptyR_is_not_reflexive
exact X
done
