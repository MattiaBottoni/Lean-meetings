import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function

open Set --I open all these features so that I can use the functions without the prefix e.g. I can write Icc instead of Set.Icc
open Function
open Real
open Nat


--exercise 5.1.1
def zero_one : Set ℝ := {x | x = 0 ∨ x = 1}

def zero_one' : Set ℝ := {0, 1}

theorem zero_one_times_R_uncountable : ¬ Countable (zero_one' × Set ℝ) := by --stimmt nicht ganz
intro h
have h1 : Countable zero_one' := by
  let f : zero_one → ℕ := λ x => if x = (0 : ℝ)  then 0 else 1
  have h2 : Injective f := by
    rw [Injective]
    intro x y
    intro h3
    cases' x with x h4
    cases' y with y h5
    simp at h3
    rw [zero_one] at h4
    cases' h4 with h40 h41
    sorry --find usa, wia h3 umschriba, denn mach alli cases.
  --exact Countable.exists_injective_nat' f h2
  sorry
have h2 : ¬ Countable (Set ℝ) := by
  intro h3
  sorry
sorry
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

def f_5_2 : F → Set (Set ℝ) := λ (f : F) => {B : Set ℝ | ∀ x : ℝ, x ∈ B ↔ f.val x = (1 : ℝ)}

lemma f_ne_one_eq_zero : ∀f : F, ¬ (f.val (x:ℝ) = (1:ℝ)) → (f.val x = (0:ℝ)) := by
intro f
intro h
cases' f with g h1
simp at *
let h2 := g x
have h3 : g x = h2 := by
  rfl
cases' h3 with g1 g2
exact g20
exfalso
apply h
simp_rw [zero_one'] at g
simp_rw [@insert_def] at g
let h2 := g x
have h3 : (g x).val = 0  ∨ (g x).val = 1 := by
  rw [h2]
--have h4 : ∃ h, ↑f x = { val := 1, property := h } := by
  --use h111
--have h1 : f.val (x:ℝ) = (0:ℝ) ∨ f.val x = (1:ℝ) := by
sorry



done

lemma f_g_eq_zero_iff_f_g_eq_one (h: ∀ (f g : F), f.val x = (1 : ℝ) ↔ g.val x = (1 : ℝ)) : ∀ (f g : F), f.val x = (0 : ℝ) ↔ g.val x = (1 : ℝ) := by

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
specialize h x
refine SetCoe.ext ?h.a
rw [@iff_eq_eq] at h
sorry
done


theorem f_5_2_is_surjective : Surjective f_5_2 := by
rw [Surjective]
intro B
--use {val := λ (x : ℝ)  => if x ∈ B then {val := 1, property := by simp[zero_one]} else {val := 0, property := by simp[zero_one]}, property := by simp[F]}
use {val := λ (x : ℝ)  => haveI := Classical.dec (x ∈ B) ; if x ∈ B then {val := 1, property := by simp[zero_one]} else {val := 0, property := by simp[zero_one]}, property := by simp[F]}
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
 cases' h4b with h4b1 h4b2
 constructor
 intro hninA
 apply h4b1
 exact hninA
 exact h4b2
rw [← h5] at h4a
exact h4a
cases' h3 with h3a h3b
exact h3a
intro h2
have h4 : ∃ C, C ∈ A1 ∧ B = {nm | ∃ n, n ∈ C ∧ nm = (n, 0)} := by
  apply hright
  use A
cases' h4 with C h4
have h6 : A = C := by
  sorry
rw [← h6] at h4
cases' h4 with h4a h4b
exact h4a
done

theorem f_5_3_inv_is_injective : Injective f_5_3_inv := by
rw [Injective]
intro B1 B2
intro h
rw [f_5_3_inv] at h
rw [f_5_3_inv] at h
simp at h
rw [ext_iff] at h
simp at h
ext B
constructor
intro h1
have A : Set ℕ := {n | ∃ (nm : ℕ × ℕ), nm ∈ B ∧ n = 2^nm.fst*3^nm.snd}
have hA : A = {n | ∃ (nm : ℕ × ℕ), nm ∈ B ∧ n = 2^nm.fst*3^nm.snd} := by
  sorry
specialize h A
cases' h with hleft hright
have h3 : ∃ C, C ∈ B2 ∧ A = {n | ∃ (nm : ℕ × ℕ), nm ∈ B ∧ n = 2^nm.fst*3^nm.snd} := by
  apply hright
  use A
done


theorem PowerN_equi_PowerNtimesN : ∃ h : Set (Set ℕ) → Set (Set (ℕ × ℕ)), Bijective h := by
exact Function.Embedding.schroeder_bernstein f_5_3_is_injective f_5_3_inv_is_injective
done



--exercise 5.4
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
