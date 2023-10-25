import Mathlib.Tactic
import Mathlib.Data.Real.Basic

variable (n : ℕ)
variable (x y : ℝ)

open Nat
open BigOperators
open Finset

example : 0 + n = n := by --try it yourself
sorry
done

example : 0 + n = n := by --solution
induction' n with d hd
rw [Nat.add_zero]
rw [Nat.add_succ]
rw [hd]
done


example : n + m = m + n := by --try it yourself
sorry
done

example : n + m = m + n := by --solution
induction' n with d hd
rw [Nat.add_zero]
rw [Nat.zero_add]
rw [Nat.add_succ]
rw [Nat.succ_add]
rw [hd]
done


example : ∑ k in range (n+1), k = n*(n+1)/(2 : ℕ) := by --It does not work yet!
sorry
done

example : ∑ k in range (n+1), k = n*(n+1)/(2 : ℕ) := by --solution
induction' n with d hd
rw [sum_range_one]
simp
rw [sum_range_succ]
rw [hd]
rw [succ_eq_add_one]
ring_nf
rw [add_comm]
--rw [div_add'] --strange
--rw [div_left_inj]
sorry
done


example : ∑ k in Finset.Ico 1 (n+1), (2*k-1) = n^2 := by --try it yourself
sorry
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
simp
linarith
linarith
done


--Exercises from the exercise sheet 3---------------------------------------------------------

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
simp
--rw [mul_div (d+1) d 2]
--rw [← mul_assoc 2 (d + 1) d / 2]
sorry
done


--exercise 3.2
example : 6 ∣ (n^3 - n) := by
induction' n with d hd
rw [pow_three]
rw [Nat.zero_mul]
rw [Nat.sub_zero]
exact Nat.dvd_zero 6
rw [succ_eq_add_one]
ring_nf
rw [← Nat.sub_sub]
rw [Nat.add_assoc]
rw [Nat.add_assoc]
rw [Nat.add_sub_self_left]
rw [← Nat.add_assoc]
rw [Nat.add_sub_assoc]
rw [← Nat.dvd_add_iff_left hd]
rw [← add_mul]
rw [pow_two]
rw [← mul_one_add]
sorry
rw [pow_three]
sorry
done

--exercise 3.3
example (k : ℕ) : (x + y) ^ n = ∑ k in range (n + 1), x^(n - k) * y^k * choose k n := by
induction' n with d hd
rw [_root_.pow_zero]
rw [Nat.zero_add]
rw [sum_range_one]
rw [Nat.choose_zero_right]
rw [_root_.pow_zero]
rw [_root_.pow_zero]
simp
rw [succ_eq_add_one]
rw [pow_add]
rw [hd]
rw [pow_one]
rw [mul_add]

sorry
done
