import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function


open Set --I open all these features so that I can use the functions without the prefix e.g. I can write Icc instead of Set.Icc
open Function
open Real


--know the ring_nf, nlinarith and norm_num tactics
example : x - y = -y + x := by
sorry
done


example : y ≤ 3 → x + y ≤ 3 + x := by
sorry
done


example : y ≤ 4 → y^2 ≤ 16 := by
sorry
done


example : (2:ℝ) + 2 = 4 := by
sorry
done



--know the have tactic
example (x y : ℝ) :  (x ^ 2 + 3 * y = y ^ 2 + 3 * x) → ((x = y) ∨ (x + y = 3)) := by
sorry
done



--know apply? and rw?
example : (x : ℝ)  = y → exp x = exp y := by
sorry
done


example : exp (x : ℝ) = exp y → x = y := by
sorry
done



--know how to define function from a set to a set
def set_even : Set ℕ := {n | Even n}

def set_odd : Set ℕ := {n | Odd n}

def even_to_odd : set_even → set_odd := λ n ↦ {val := (n + 1), property := by simp[set_even] ; exact Even.add_one n.prop}


example : Injective even_to_odd := by
sorry
done


example : Surjective even_to_odd := by
sorry
done



--Proof that a relation is an equivalence relation
def R_4_dvd (x y : ℤ) : Prop := 4 ∣ (x + 3*y)


theorem R_4_dvd_is_reflexive : Reflexive R_4_dvd := by
sorry
done


theorem R_4_dvd_is_symmetric : Symmetric R_4_dvd := by
sorry
done


theorem R_4_dvd_is_transitive : Transitive R_4_dvd := by
sorry
done



--Proof that a function is bijective
def f_linear_Q : ℚ → ℚ := λ x => 2*x + 1


theorem f_linear_Q_is_injective : Injective f_linear_Q := by
sorry
done


theorem f_linear_Q_is_surjective : Surjective f_linear_Q := by
sorry
done


theorem f_linear_Q_is_bijective : Bijective f_linear_Q := by
sorry
done



--Proof that two sets have equal cardinality by finding a bijection between them
--A and B have equal cardinality
def A : Set ℚ := {3*k | k : ℚ}

def B : Set ℚ := {7*k | k : ℚ}

def f_A_B : A → B := λ k ↦ {val := (7:ℚ) * (k/3:ℚ), property := by simp [B]}


theorem f_A_B_is_injective : Injective f_A_B := by
sorry
done


theorem f_A_B_is_surjective : Surjective f_A_B := by
sorry
done


theorem f_A_B_is_bijective : Bijective f_A_B := by
sorry
done
