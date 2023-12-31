import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.SetTheory.Cardinal.SchroederBernstein


open Set --I open all these features so that I can use the functions without the prefix e.g. I can write Icc instead of Set.Icc
open Function
open Real


--Exercises from exercise sheet 4---------------------------------------------------------

--exercise 4.1.
def R_even : ℤ → ℤ → Prop := λ x y ↦ Even (x^2 + y^2)


theorem R_even_is_reflexive : Reflexive R_even := by --This first exercises is pretty easy. Have a look at level 3 exercise 4.
sorry
done


theorem R_even_is_symmetric : Symmetric R_even := by
sorry
done


theorem R_even_is_transitive : Transitive R_even := by
sorry
done


--alternative exericse 4.1.
--here I do not define the relation beforehand. I just write the definition of the relation in the theorem statement.
theorem R_sq_is_reflexive : ∀x : ℤ,  Even (x^2 + x^2) := by --Try to understand the difference between the two proofs.
sorry
done


theorem R_sq_is_symmetric : ∀ x y : ℤ, Even (x^2 + y^2) → Even (y^2 + x^2) := by
sorry
done


theorem R_sq_is_transitive : ∀ x y z : ℤ, (Even (x^2 + y^2) ∧ Even (y^2 + z^2)) → Even (x^2 + z^2) := by
sorry
done



--exercise 4.2.
--We will do this on paper.



--exercise 4.3.
def f : (ℤ × ℤ) → (ℤ × ℤ) := λ (m, n) ↦ (m + n, 2*m + n)


example : f (2, 3)  = (5, 7) := by
rfl
done


theorem f_is_injective : Injective f := by --Always start with "rw [Injective]". Then, try to prove the statement.
sorry
done


theorem f_is_surjective : Surjective f := by
sorry
done


theorem f_is_bijective : Bijective f := by --Start with "rw [Bijective]", then exact the two theorems from above. But use "constructor" first!
sorry
done



--exercise 4.4.1
def f_4_4_1 : ℝ → ℝ := λ x ↦ x^2 + 3


example : image f_4_4_1 (Icc 3 5) = Icc 12 28 := by --I recommend you to do these two on paper first. They are quite a challenge in Lean.
sorry
done


example : preimage f_4_4_1 (Icc 12 19) = ((Icc 3 4) ∪ (Icc (-4) (-3))) := by --This one took me hours to finish!
sorry
done


--exercise 4.4.2
section

variable (A B : Type)
variable (X Y : Set A)
variable (g : A → B)


example : g '' (X ∩ Y) ⊆ g '' X ∩ g '' Y := by --Don't get scared from the notation. You can prove this only using tactics from level 1 and the tactic "use".
sorry
done


example : g '' (X ∩ Y) ⊆ g '' X ∩ g '' Y := by
sorry
done


--exercise 4.4.3
--we will do this on paper.
end



--exercise 4.5.1
def set_B : Set ℝ := {y | sqrt 2 < y}


noncomputable def f_4_5_1_bounded : ℝ → set_B :=
λ x ↦ {val := sqrt 2 + exp x, property := by simp [set_B] ;   exact exp_pos x}


theorem f_4_5_1_is_injective : Injective f_4_5_1_bounded := by --The concept of the proof is rather easy. But you will need to use some tactics that are quite unique. Try it with "apply?" and "exact?" or go through the solutions.
sorry
done


theorem f_4_5_1_is_surjective : Surjective f_4_5_1_bounded := by
sorry
done


theorem f_4_5_1_is_bijective : Bijective f_4_5_1_bounded := by
sorry
done


--exercise 4.5.2 --using cantor schroeder bernstein theorem
def set_A : Set (ℕ × ℕ) := { mn | mn.1 ≤ mn.2 }

def f_4_5_2a : set_A  → ℕ × ℕ := λ mn ↦ (mn.val.2, mn.val.1)

def f_4_5_2b :  ℕ × ℕ → set_A := λ (n,m) ↦ {val := (n,n + m), property := by simp [set_A]}


theorem f_4_5_2_a_is_injective : Injective f_4_5_2a := by --Again, the concept is pretty easy. But some tactics are special. The solutions can help you.
sorry
done


theorem f_4_5_2_b_is_injective : Injective f_4_5_2b := by
sorry
done


theorem set_A_equi_NtimesN : ∃ h : set_A →  ℕ × ℕ, Bijective h := by
sorry
done


--other approach for 4.5.2.
def set_A_N : (N : ℕ)  →  Set (ℕ × ℕ) := λN ↦ { mn | mn.1 ≤ mn.2 ∧  mn.2 ≤ N }

def set_n_leq_N : (N : ℕ) → Set ℕ  := λ N ↦ {n | n ≤ N}

def set_n_leq_N_cross : (N : ℕ) → Set (set_n_leq_N N × set_n_leq_N N)  := λ_ ↦ {n | (n.1 = n.2)}

--def set_n_leq_N_cross' : (N : ℕ) → Set (ℕ × ℕ)  := λ N ↦ {n | (n.1 = n.2) ∧ n.1 ≤ N}

theorem set_n_leq_N_cross_is_finite : ∀ N : ℕ, Finite (set_n_leq_N_cross N) := by --I was not able to prove all these theorems in Lean. I think it is better to just undestand the theorems written here and figure out how to puzzle them together to solve the actual exercise.
sorry
done


theorem set_A_N_is_finite : ∀ N : ℕ, Finite (set_A_N N) := by
sorry
done


theorem set_A_N_is_countable : ∀ N : ℕ, Countable (set_A_N N) := by
sorry
done


def set_union_A : Set (ℕ × ℕ) := ⋃ N : ℕ, set_A_N N


theorem set_union_A_is_countable : Countable set_union_A := by
sorry
done


def set_B_in_A : Set (ℕ × ℕ) := {n | n.1 = n.2}


theorem set_B_in_A_is_infinite : Infinite set_B_in_A := by
sorry
done


theorem set_B__in_A_is_in_A : set_B_in_A ⊆ set_union_A := by
sorry
done


theorem set_union_A_is_infinite : Infinite set_union_A := by
sorry
done



--exercise 4.6
theorem comp_is_bijective : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z), Bijective f → Bijective g → Bijective (g ∘ f) := by --Since we can use this, I give you the proof. If you want to try it yourself, delete the proof.
intro X
intro Y
intro Z
intro f
intro g
intro h1
intro h2
rw [Bijective]
cases' h1 with hf1 hf2
cases' h2 with hg1 hg2
constructor
rw [Injective]
intro x
intro y
intro h
rw [Function.comp] at h
rw [Injective] at hf1
rw [Injective] at hg1
exact hf1 (hg1 h)
rw [Surjective]
intro z
rw [Surjective] at hf2
rw [Surjective] at hg2
cases' hg2 z with y hy
cases' hf2 y with x hx
use x
rw [Function.comp]
simp at *
rw [hx]
rw [hy]
done


def R_card (X Y : Type) : Prop := ∃ f : X → Y, Bijective f


theorem R_card_is_reflexive : Reflexive R_card := by --Type "use id" to use the identity relation here.
sorry
done


theorem R_card_is_symmetric : Symmetric R_card := by --This is the most difficult one out of these three. Think about how you would solve this on paper. Then, compare it to the solution.
sorry
done


theorem R_card_is_transitive : Transitive R_card := by --At the end of this proof you will need to type "use g ∘ f" and then "exact comp_is_bijective f g hf hg".
sorry
done
