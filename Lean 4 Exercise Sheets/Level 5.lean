import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function

open Set --I open all these features so that I can use the functions without the prefix e.g. I can write Icc instead of Set.Icc
open Function
open Real
open Nat


--Exercises from exercise sheet 5---------------------------------------------------------

--exercise 5.1.1
def zero_one : Set ℝ := {x | x = 0 ∨ x = 1}

def zero_one' : Set ℝ := {0, 1}


theorem zero_one_times_R_uncountable : ¬ Countable (zero_one' × Set ℝ) := by --Please don't try this exercise. I spent a whole morning on this and I still was not able to finish it.
sorry
done


--exercise 5.1.2
section
variable (α : Type _)
variable (A B : Set α)

open Set


example (h : (A ⊆ B ∧ Set.Countable A ∧ ¬ Set.Countable B)) : ¬ Set.Countable (B \ A) := by --This one has a nice twist. Try to do it on your own or have a quick glimpse at the solutions.
sorry
end



--exercise 5.2
def F : Set (ℝ → zero_one') := Set.univ

def f_5_2 : F → Set (Set ℝ) := λ (f : F) => {B : Set ℝ | ∀ x : ℝ, x ∈ B ↔ f.val x = (1 : ℝ)}

lemma f_ne_one_eq_zero : ∀f : F, ¬ (f.val (x:ℝ) = (1:ℝ)) ↔ (f.val x = (0:ℝ)) := by --This Lemma should help the next theorems.
sorry
done

lemma f_g_eq_zero_iff_f_g_eq_one (f g : F) : (f.val x = (1 : ℝ) ↔ g.val x = (1 : ℝ)) → f.val x = g.val x := by
intro h
have h1 : f.val x = (0 : ℝ) ∨ f.val x = (1 : ℝ) := by
  by_cases h2 : f.val x = (1 : ℝ)
  right
  exact h2
  left
  rw [f_ne_one_eq_zero] at h2
  exact h2
have h3 : g.val x = (0 : ℝ) ∨ g.val x = (1 : ℝ) := by
  by_cases h2 : g.val x = (1 : ℝ)
  right
  exact h2
  left
  rw [f_ne_one_eq_zero] at h2
  exact h2
cases' f with f hf
cases' g with g hg
simp at *
cases' h1 with hf0 hf1
cases' h3 with hg0 hg1
symm at hg0
rw [hg0] at hf0
exact SetCoe.ext hf0
have hf1 : ↑(f x) = (1 : ℝ)  := by
  rw [← h] at hg1
  exact hg1
symm at hg1
rw [hg1] at hf1
exact SetCoe.ext hf1
cases' h3 with hg0 hg1
have hg1 : ↑(g x) = (1 : ℝ)  := by
  rw [h] at hf1
  exact hf1
symm at hg1
rw [hg1] at hf1
exact SetCoe.ext hf1
symm at hg1
rw [hg1] at hf1
exact SetCoe.ext hf1
done


theorem f_5_2_is_injective : Injective f_5_2 := by --If you are able to understand the definitions, notations and lemmas above, you have done more than enough.
sorry
done


theorem f_5_2_is_surjective : Surjective f_5_2 := by --I have not been able to prove this in Lean myself.
sorry
done


theorem f_5_2_is_bijective : Bijective f_5_2 := by
sorry
done



--exercise 5.3
def f_5_3 : Set (Set ℕ) → Set (Set (ℕ × ℕ)) := λ (A : Set (Set ℕ)) => {B | ∃ (C : Set ℕ), C ∈ A ∧ B = {nm | ∃ (n : ℕ), n ∈ C ∧ nm = (n, 0)}}

def f_5_3_inv : Set (Set (ℕ × ℕ)) → Set (Set ℕ) := λ (A : Set (Set (ℕ × ℕ))) => {B | ∃ (C : Set (ℕ × ℕ)), C ∈ A ∧ B = {n | ∃ (nm : ℕ × ℕ), nm ∈ C ∧ n = 2^nm.fst*3^nm.snd}}


theorem f_5_3_is_injective : Injective f_5_3 := by --From the red exercises of sheet 5, this is the "easiest". It is a long and sophisticated proof, but contrary to the other two exercises (5.1.1 and 5.2), it is complete.
sorry
done

theorem eq_prime_factorization (a b x y : ℕ) : 2 ^ a * 3 ^ b = 2 ^ x * 3 ^ y ↔ ((a = x) ∧ (b = y)) := by --I have no clue how to proof this in Lean. Maybe you know ;)
sorry --we know that the prime factorization of any two numbers is unique
done

theorem f_5_3_inv_is_injective : Injective f_5_3_inv := by --When using the theorem above, this proof is doable (but really long).
sorry
done


theorem PowerN_equi_PowerNtimesN : ∃ h : Set (Set ℕ) → Set (Set (ℕ × ℕ)), Bijective h := by --This is just one line, namely how to use Bernstein-Schröder in Lean.
sorry
done



--exercise 5.4 (Addition on ℕ)
example : ∀ x : ℕ, zero + x = x := by --Finally, some simple exercises in level 5! For some reason, you need to write Nat. here first.
sorry
done


example : ∀ x y : ℕ, succ y + x = succ (y + x) := by
sorry
done


example : ∀ x : ℕ, zero * x = zero := by
sorry
done


example : ∀ x : ℕ, succ zero * x = x := by
sorry
done

/-For more natural number exercises, to the natural number game online!-/
