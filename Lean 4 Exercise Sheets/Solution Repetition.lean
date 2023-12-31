import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function


open Set --I open all these features so that I can use the functions without the prefix e.g. I can write Icc instead of Set.Icc
open Function
open Real


--know the ring_nf, nlinarith and norm_num tactics
example : x - y = -y + x := by
ring_nf
done


example : y ≤ 3 → x + y ≤ 3 + x := by
intro h
linarith
done


example : y ≤ 4 → y^2 ≤ 16 := by
intro h
nlinarith
done


example : (2:ℝ) + 2 = 4 := by
norm_num
done



--know the have tactic
example (x y : ℝ) :  (x ^ 2 + 3 * y = y ^ 2 + 3 * x) → ((x = y) ∨ (x + y = 3)) := by
intro h
have h1 : (x - y) * (x + y - 3) = 0 := by
  ring_nf
  rw [← sub_eq_zero] at h
  ring_nf at h
  exact h
  done
rw [mul_eq_zero] at h1
cases' h1 with hxy hxy3
left
rw [sub_eq_zero] at hxy
exact hxy
right
rw [sub_eq_zero] at hxy3
exact hxy3
done



--know apply? and rw?
example : (x : ℝ)  = y → exp x = exp y := by
intro h
exact congrArg rexp h
done


example : exp (x : ℝ) = exp y → x = y := by
intro h
rw [exp_eq_exp] at h
exact h
done



--know how to define function from a set to a set
def set_even : Set ℕ := {n | Even n}

def set_odd : Set ℕ := {n | Odd n}

def even_to_odd : set_even → set_odd := λ n ↦ {val := (n + 1), property := by simp[set_even] ; exact Even.add_one n.prop}


example : Injective even_to_odd := by
rw [Injective]
intro x y
intro h
rw [even_to_odd] at h
rw [even_to_odd] at h
simp at *
rw [SetCoe.ext_iff] at h
exact h
done


example : Surjective even_to_odd := by
rw [Surjective]
intro y
cases' y with y hy
rw [set_odd] at hy
use {val := (y - 1), property := by simp[set_even] ; have h1 : Odd 1 ; simp ; exact Nat.Odd.sub_odd hy h1}
rw [even_to_odd]
simp at hy
simp
rw [tsub_add_cancel_iff_le]
rw [Nat.one_le_iff_ne_zero]
intro h
rw [h] at hy
apply hy
simp
done



--Proof that a relation is an equivalence relation
def R_4_dvd (x y : ℤ) : Prop := 4 ∣ (x + 3*y)


theorem R_4_dvd_is_reflexive : Reflexive R_4_dvd := by
rw [Reflexive]
intro x
rw [R_4_dvd]
rw [← one_add_mul 3 x]
norm_num
done


theorem R_4_dvd_is_symmetric : Symmetric R_4_dvd := by
rw [Symmetric]
intro x y
rw [R_4_dvd]
rw [R_4_dvd]
intro h
cases' h with k hk
have hk2 : x = 4*k - 3*y := by
  rw [← hk]
  ring
rw [hk2]
rw [mul_sub]
rw [← add_sub_assoc]
rw [add_sub_right_comm]
rw [← mul_assoc]
have h3 : y - 3 * 3 * y = -8 * y := by
  ring
rw [h3]
have h4 : 4 ∣ -8 * y := by
  norm_num
  have h4 : (4 : ℤ)  ∣ 8 := by
    norm_num
  exact dvd_mul_of_dvd_left h4 y
rw [dvd_add_right h4]
rw [mul_comm]
ring_nf
rw [mul_comm]
have h5 : (4 : ℤ)  ∣ 12 := by
  norm_num
exact dvd_mul_of_dvd_left h5 k
done


theorem R_4_dvd_is_transitive : Transitive R_4_dvd := by
rw [Transitive]
intro x y z
rw [R_4_dvd]
rw [R_4_dvd]
rw [R_4_dvd]
intro hxy
intro hyz
have h1 : 4 ∣ x + 3 * y + y + 3 * z := by
  rw [add_assoc]
  exact dvd_add hxy hyz
have h2 : 3 * y + y = 4 * y := by
  ring
rw [add_comm] at h1
rw [← add_assoc] at h1
rw [← add_assoc] at h1
rw [add_assoc] at h1
rw [h2] at h1
have h3 : 4 ∣ (4 * y) := by
  norm_num
rw [dvd_add_left h3] at h1
rw [add_comm]
exact h1
done



--Proof that a function is bijective
def f_linear_Q : ℚ → ℚ := λ x => 2*x + 1


theorem f_linear_Q_is_injective : Injective f_linear_Q := by
rw [Injective]
intro x y
rw [f_linear_Q]
rw [f_linear_Q]
intro h
rw [add_left_inj] at h
rw [← sub_eq_zero] at h
rw [← mul_sub] at h
rw [mul_eq_zero] at h
cases' h with h1 h2
have h2 : ((2:ℚ)  ≠ 0) := by
  norm_num
exfalso
apply h2
exact h1
rw [sub_eq_zero] at h2
exact h2
done


theorem f_linear_Q_is_surjective : Surjective f_linear_Q := by
rw [Surjective]
intro y
use (y - 1) / 2
rw [f_linear_Q]
ring
done


theorem f_linear_Q_is_bijective : Bijective f_linear_Q := by
rw [Bijective]
constructor
exact f_linear_Q_is_injective
exact f_linear_Q_is_surjective
done



--Proof that two sets have equal cardinality
--A and B have equal cardinality
def A : Set ℚ := {3*k | k : ℚ}

def B : Set ℚ := {7*k | k : ℚ}

def f_A_B : A → B := λ k ↦ {val := (7:ℚ) * (k/3:ℚ), property := by simp [B]}


theorem f_A_B_is_injective : Injective f_A_B := by
rw [Injective]
intro x y
intro h
rw [f_A_B] at h
rw [f_A_B] at h
simp at *
rw [div_left_inj'] at h
rw [SetCoe.ext_iff] at h
exact h
norm_num
done


theorem f_A_B_is_surjective : Surjective f_A_B := by
rw [Surjective]
intro y
cases' y with y hy
use {val := (3:ℚ) * (y/7:ℚ), property := by simp[A]}
rw [f_A_B]
simp
ring
done


theorem f_A_B_is_bijective : Bijective f_A_B := by
rw [Bijective]
constructor
exact f_A_B_is_injective
exact f_A_B_is_surjective
done
