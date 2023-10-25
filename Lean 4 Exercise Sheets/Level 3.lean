import Mathlib.Tactic
import Mathlib.Data.Real.Basic

variable (n : ℕ)
--variable (x y : ℝ)

open Nat
open BigOperators
open Finset



example : 0 + n = n := by
induction' n with d hd
rw [Nat.add_zero]
rw [Nat.add_succ]
rw [hd]
done


example : n + m = m + n := by
induction' n with d hd
rw [Nat.add_zero]
rw [Nat.zero_add]
rw [Nat.add_succ]
rw [Nat.succ_add]
rw [hd]
done


example: ∑ k in range (n+1), k = (n*(n+1))/2 := by
induction' n with d hd
rw [Nat.zero_mul]
sorry
rw [succ_eq_add_one]
rw [sum_range_succ]
rw [hd]

done


example : ∑ k in Finset.Ico 1 n, 2*k-1 = n^2 := by
induction' n with d hd
simp
rw [succ_eq_add_one]
rw [sum_Ico_succ_top]
sorry
sorry
done


--Exercises from the exercise sheet 3---------------------------------------------------------

--exercise 3.1
example : ((Finset.range n).sum Nat.succ) ^ 2 = (Finset.range n).sum (λ k ↦ k^3) := by
induction' n with d hd
sorry
sorry
done

--exercise 3.1
example : (∑ k in range n, k)^2 = ∑ k in range n, k^3 := by
induction' n with d hd
sorry
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
--rw [← Nat.add_sub]
--rw [← Nat.dvd_add_iff_left hd]
sorry
done

--exercise 3.3
example (k : ℕ) : (x + y) ^ n = ∑ k in range (n + 1), x^(n - k) * y^k * Nat.choose k n := by
induction' n with d hd
rw [_root_.pow_zero]
rw [Nat.zero_add]
rw [Nat.choose_zero_right]
sorry
sorry
done
