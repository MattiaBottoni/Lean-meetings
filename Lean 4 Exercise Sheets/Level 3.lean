import Mathlib.Tactic
import Mathlib.Data.Real.Basic

variable (n : ℕ)
--variable (x y : ℝ)

open Nat
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
rw [Nat.add_zero]
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
simp
linarith
linarith
done


example : ∑ i in range (n+1), (i:ℚ) = (n:ℚ)*(n+1)/2 := by --try it yourself, this is a bit difficult
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

example : ∑ k in range (n+1), (k:ℚ) = (n:ℚ)*(n+1)/(2 : ℚ) := by --solution
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
ring_nf
simp
have h2 : 2 ∣ d * d + d
rw [← mul_add_one] --find 2 dvd n, n+1)
sorry
rw [Nat.div_mul_cancel]
rw [mul_assoc]
rw [Nat.div_mul_cancel]
ring
exact h2
exact h2
done


lemma aux1 : ∑ k in range n, (k : ℚ) = (n : ℚ) * (n - 1) / 2 := by --by Kevin Buzzard
  induction n with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ih, succ_eq_add_one]
    push_cast
    ring

lemma aux2 : ∑ k in range n, (k : ℚ) ^3 = ((n : ℚ) * (n - 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ih, succ_eq_add_one]
    push_cast
    ring

-- remark: aux1 and aux2 have exactly the same proof.

example : (∑ k in range (n+1), k)^2 = ∑ k in range (n+1), k^3 := by
  qify
  rw [aux1, aux2]


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
rw [← mul_one_add] --divide by 3, use again 2 dvd n, n+1
--by_cases d = 2*k
sorry
rw [three_eq_succ_succ_succ_zero]
exact Nat.le_self_pow
done


example : 6 ∣ (n^3 - n) := by
 induction' n using Nat.twoStepInduction with d hd hd2
 simp
 simp
 rw [succ_eq_add_one]
 rw [add_assoc]
 rw [one_add_one_eq_two]
 ring_nf
 have h2 : 6 ∣ 8-2
 simp
 have h3 : 6 ∣ d * 12
 sorry
 have h4 : 6 ∣ d ^ 2 * 6
 simp
 rw [add_comm 8]
 rw [add_assoc]
 rw [add_assoc]
 rw [Nat.add_sub_assoc]
 rw [← Nat.dvd_add_iff_right h3]
 rw [add_comm]
 rw [Nat.add_sub_assoc]
 rw [add_assoc]
 rw [← Nat.dvd_add_iff_right h4]
 rw [← Nat.sub_sub]
 rw [← Nat.add_sub_assoc]
 rw [add_comm]
 rw [Nat.add_sub_assoc]
 rw [← Nat.dvd_add_iff_right h2]
 exact hd
 sorry
 sorry
 sorry
 sorry
done


--exercise 3.3
example (k : ℕ) : (x + y) ^ n = ∑ k in range (n + 1), x^(n - k) * y^k * Nat.choose k n := by
induction' n with d hd
rw [Nat.pow_zero]
rw [Nat.zero_add]
rw [sum_range_one]
rw [Nat.choose_zero_right]
rw [Nat.pow_zero]
rw [Nat.pow_zero]
rw [succ_eq_add_one]
rw [pow_add]
rw [hd]
rw [pow_one]
rw [mul_add]
rw [sum_range_succ] --I want Lean to do this only to the first sum
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
conv_lhs => rw [sum_range_succ'] --and this to the second sum
sorry
done


--exercise 3.4.1
section
variable (x y : ℤ)
theorem R_is_reflexive : |x-x| < 1 := by
rw [sub_self]
rw [abs_zero]
linarith
done


theorem R_is_symmetric (h : |x-y|<1) : |y-x| < 1 := by
rw [abs_sub_comm]
exact h
done


theorem R_is_transitive (hxy : |x-y| < 1) (hyz : |y-z| < 1) : |x-z| < 1 := by
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


--exercise 3.4.2
theorem R_le_is_reflexive : |x-x| ≤ 1 := by
rw [sub_self]
rw [abs_zero]
linarith
done


theorem R_le_is_symmetric (h : |x-y| ≤ 1) : |y-x| ≤ 1 := by
rw [abs_sub_comm]
exact h
done

theorem R_le_is_not_transitive (hxy : |x-y| ≤ 1) (hyz : |y-z| ≤ 1) : |x-z| ≤ 1 := by
rw [← add_zero x]
rw [← sub_self y]
rw [← add_comm_sub]
rw [← add_sub]
by_contra h1
sorry
done
end



--exercise 3.5
section
variable
  {X : Sort _}
  (x y a : X)
  (R : X → X → Prop)
  (empty_R : X → X → Prop)
open Set

theorem empty_R_is_symmetric (h : ∀ ⦃x y : X⦄, empty_R x y = False): Symmetric empty_R := by
rw [Symmetric]
intro x
intro y
intro h2
rw [h] at h2
exfalso
exact h2
done


theorem empty_R_is_transitive (h : ∀ ⦃x y : X⦄, empty_R x y = False): Transitive empty_R := by
rw [Transitive]
intro x
intro y
intro z
intro h2
intro h3
rw [h] at h2
exfalso
exact h2
done


theorem empty_R_is_not_reflexive (h : ∀ ⦃x y : X⦄, empty_R x y = False): ¬Reflexive empty_R := by
rw [Reflexive]
intro h2
specialize h2 x
rw [h] at h2
exact h2
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
--we will do this on paper.

end
