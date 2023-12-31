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


theorem zero_one_times_R_uncountable : ¬ Countable (zero_one' × Set ℝ) := by
intro h
have h1 : Countable zero_one' := by
  let f : zero_one → ℕ := λ x => if x = (0 : ℝ)  then 0 else 1
  have h2 : Injective f := by
    rw [Injective]
    intro x y
    intro h3
    cases' x with x h4
    cases' y with y h5
    simp at *
    simp_rw [zero_one] at h4
    simp_rw [zero_one] at h5
    rw [@ite_eq_iff] at h3
    cases' h4 with h40 h41
    cases' h5 with h50 h51
    symm at h50
    rw [← h40] at h50
    exact h50
    cases' h3 with h30 h31
    rw [@eq_ite_iff] at h30
    cases' h30 with h30 h32
    cases' h32 with h32 h34
    cases' h32 with h32 h34
    exfalso
    rw [h32] at h51
    norm_num at h51
    cases' h34 with h34 h36
    exfalso
    norm_num at h36
    cases' h31 with h31 h33
    exfalso
    apply h31
    exact h40
    cases' h5 with h50 h51
    cases' h3 with h30 h31
    cases' h30 with h30 h32
    rw [h30] at h41
    exfalso
    norm_num at h41
    cases' h31 with h31 h33
    rw [if_pos h50] at h33
    exfalso
    norm_num at h33
    rw [h41]
    rw [← h51]
  rw [countable_coe_iff]
  rw [Set.countable_iff_exists_injective]
  use f
have h2 : ¬ Countable (Set ℝ) := by
  intro h3
  rw [countable_iff_exists_injective] at h3
  sorry
rw [@countable_coe_iff] at h1
rw [← @countable_univ_iff] at h
rw [← @countable_univ_iff] at h2
have h3 : Set.Countable zero_one' ∧ Countable (Set ℝ) := by
  constructor
  exact h1
  rw [← @univ_prod_univ] at h
  rw []
done


--exercise 5.1.2
section
variable (α : Type _)
variable (A B : Set α)

open Set


example (h : (A ⊆ B ∧ Set.Countable A ∧ ¬ Set.Countable B)) : ¬ Set.Countable (B \ A) := by
cases' h with h1 h2
cases' h2 with h2 h3
intro h4
have h5 : Set.Countable (A ∪ (B \ A)) := by
  rw [Set.countable_union]
  constructor
  exact h2
  exact h4
have h6 : B = A ∪ (B \ A) := by
  rw [Set.union_diff_cancel h1]
rw [← h6] at h5
apply h3
exact h5
done
end



--exercise 5.2
def F : Set (ℝ → zero_one') := Set.univ

def f_5_2 : F → Set (Set ℝ) := λ (f : F) => {B | ∀ x : ℝ, x ∈ B ↔ f.val x = (1 : ℝ)}


lemma f_ne_one_eq_zero : ∀f : F, ¬ (f.val (x:ℝ) = (1:ℝ)) ↔ (f.val x = (0:ℝ)) := by
intro f
constructor
intro h
cases' f with g h1
simp at *
rw?
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


theorem f_5_2_is_injective : Injective f_5_2 := by
rw [Injective]
intro f g
intro h
rw [f_5_2] at h
rw [f_5_2] at h
rw [ext_iff] at h
simp at h
refine SetCoe.ext ?_
refine funext ?h
intro x
let B : Set ℝ  := {x | f.val x = (1 : ℝ)}
specialize h B
refine SetCoe.ext ?h.a
rw [@iff_eq_eq] at h
simp at *
specialize h x
have h2 : f.val x = g.val x := by
  exact f_g_eq_zero_iff_f_g_eq_one f g h
simp at *
exact congrArg Subtype.val h2
done


theorem f_5_2_is_surjective : Surjective f_5_2 := by
rw [Surjective]
intro A
--use {val := λ (x : ℝ)  => ∀b : B, val := if x ∈ B then {val := 1, property := by simp[zero_one']} else {val := 0, property := by simp[zero_one']}, property := by simp[F]}
use {val := (λ (x : ℝ)  => ∀(B : A), if x ∈ B then {val := 1, property := by simp[zero_one']} else {val := 0, property := by simp[zero_one']}), property := by simp[F]}
rw [f_5_2]
simp
rw [ext_iff]
intro x
constructor
intro h

done


theorem f_5_2_is_bijective : Bijective f_5_2 := by
rw [Bijective]
constructor
exact f_5_2_is_injective
exact f_5_2_is_surjective
done



--exercise 5.3
def f_5_3 : Set (Set ℕ) → Set (Set (ℕ × ℕ)) := λ (A : Set (Set ℕ)) => {B | ∃ (C : Set ℕ), C ∈ A ∧ B = {nm | ∃ (n : ℕ), n ∈ C ∧ nm = (n, 0)}}

def f_5_3_inv : Set (Set (ℕ × ℕ)) → Set (Set ℕ) := λ (A : Set (Set (ℕ × ℕ))) => {B | ∃ (C : Set (ℕ × ℕ)), C ∈ A ∧ B = {n | ∃ (nm : ℕ × ℕ), nm ∈ C ∧ n = 2^nm.fst*3^nm.snd}}


theorem f_5_3_is_injective : Injective f_5_3 := by
rw [Injective]
intro A1 A2
intro h
rw [f_5_3] at h
rw [f_5_3] at h
rw [ext_iff] at h
simp at *
rw [ext_iff]
intro A
let B : Set (ℕ × ℕ):= {nm | ∃ (n : ℕ), n ∈ A ∧ nm = (n, 0)}
specialize h B
cases' h with hleft hright
constructor
intro h1
have h3 : ∃ C, C ∈ A1 ∧ B = {nm | ∃ n, n ∈ C ∧ nm = (n, 0)} := by
  use A
have h4 := hleft h3
cases' h4 with C h4
cases' h4 with h4a h4b
simp at h4b
have h5 : A = C := by
 rw [ext_iff]
 intro n
 rw [ext_iff] at h4b
 specialize h4b (n,0)
 simp at h4b
 exact h4b
rw [← h5] at h4a
exact h4a
intro h1
have h3 : ∃ C, C ∈ A2 ∧ B = {nm | ∃ n, n ∈ C ∧ nm = (n, 0)} := by
  use A
have h4 := hright h3
cases' h4 with C h4
cases' h4 with h4a h4b
simp at h4b
have h5 : A = C := by
 rw [ext_iff]
 intro n
 rw [ext_iff] at h4b
 specialize h4b (n,0)
 simp at h4b
 exact h4b
rw [← h5] at h4a
exact h4a
done


theorem eq_prime_factorization (a b x y : ℕ) : 2 ^ a * 3 ^ b = 2 ^ x * 3 ^ y ↔ ((a = x) ∧ (b = y)) := by
sorry --we know that the prime factorization of any two numbers is unique
done


theorem f_5_3_inv_is_injective : Injective f_5_3_inv := by
rw [Injective]
intro A1 A2
intro h
rw [f_5_3_inv] at h
rw [f_5_3_inv] at h
rw [ext_iff] at h
simp at *
rw [ext_iff]
intro A
let B : Set ℕ := {n | ∃ a b, (a,b) ∈ A ∧ n = 2^a*3^b}
specialize h B
cases' h with hleft hright
constructor
intro h1
have h3 : ∃ C, C ∈ A1 ∧ B = {n | ∃ a b, (a,b) ∈ C ∧ n = 2^a*3^b} := by
  use A
have h4 := hleft h3
cases' h4 with C h4
cases' h4 with h4a h4b
simp at h4b
have h5 : A = C := by
 rw [ext_iff]
 intro (a,b)
 rw [ext_iff] at h4b
 specialize h4b (2 ^ a * 3 ^ b)
 simp at h4b
 cases' h4b with h4lb h4rb
 simp at h4lb
 simp at h4rb
 specialize h4lb a b
 specialize h4rb a b
 simp at h4lb
 simp at h4rb
 constructor
 intro ha
 have hC := h4lb ha
 cases' hC with x hC1
 cases' hC1 with y hC2
 cases' hC2 with hC heq
 rw [eq_prime_factorization] at heq
 cases' heq with heql heqr
 rw [← heql] at hC
 rw [← heqr] at hC
 exact hC
 intro hc
 have hA := h4rb hc
 cases' hA with x hA1
 cases' hA1 with y hA2
 cases' hA2 with hA heq
 rw [eq_prime_factorization] at heq
 cases' heq with heql heqr
 rw [← heql] at hA
 rw [← heqr] at hA
 exact hA
rw [← h5] at h4a
exact h4a
intro h1
have h3 : ∃ C, C ∈ A2 ∧ B = {n | ∃ a b, (a,b) ∈ C ∧ n = 2^a*3^b} := by
  use A
have h4 := hright h3
cases' h4 with C h4
cases' h4 with h4a h4b
simp at h4b
have h5 : A = C := by
 rw [ext_iff]
 intro (a,b)
 rw [ext_iff] at h4b
 specialize h4b (2 ^ a * 3 ^ b)
 simp at h4b
 cases' h4b with h4lb h4rb
 simp at h4lb
 simp at h4rb
 specialize h4lb a b
 specialize h4rb a b
 simp at h4lb
 simp at h4rb
 constructor
 intro ha
 have hC := h4lb ha
 cases' hC with x hC1
 cases' hC1 with y hC2
 cases' hC2 with hC heq
 rw [eq_prime_factorization] at heq
 cases' heq with heql heqr
 rw [← heql] at hC
 rw [← heqr] at hC
 exact hC
 intro hc
 have hA := h4rb hc
 cases' hA with x hA1
 cases' hA1 with y hA2
 cases' hA2 with hA heq
 rw [eq_prime_factorization] at heq
 cases' heq with heql heqr
 rw [← heql] at hA
 rw [← heqr] at hA
 exact hA
rw [← h5] at h4a
exact h4a
done


theorem PowerN_equi_PowerNtimesN : ∃ h : Set (Set ℕ) → Set (Set (ℕ × ℕ)), Bijective h := by
exact Function.Embedding.schroeder_bernstein f_5_3_is_injective f_5_3_inv_is_injective
done



--exercise 5.4 (Addition on ℕ)
example : ∀ x : ℕ, zero + x = x := by
intro x
induction' x with d hd
rw [Nat.add_zero]
rw [Nat.add_succ]
rw [hd]
done


example : ∀ x y : ℕ, succ y + x = succ (y + x) := by
intros x y
induction' x with d hd
rw [Nat.add_zero]
rw [Nat.add_succ]
rw [hd]
rw [Nat.add_succ]
done


example : ∀ x : ℕ, zero * x = zero := by
intro x
induction' x with d hd
rw [Nat.mul_zero]
rw [Nat.mul_succ]
rw [hd]
done


example : ∀ x : ℕ, succ zero * x = x := by
intro x
induction' x with d hd
rw [Nat.mul_zero]
rw [Nat.mul_succ]
rw [hd]
done
