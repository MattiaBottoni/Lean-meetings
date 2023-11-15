import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function

open Set
open Function
open Real


--exercise 4.1.
def R_even : ℤ → ℤ → Prop := λ x y ↦ Even (x^2 + y^2)


theorem R_even_is_reflexive : Reflexive R_even := by
rw [Reflexive]
intro x
rw [R_even]
rw [← two_mul]
apply even_two_mul
done


theorem R_even_is_symmetric : Symmetric R_even := by
rw [Symmetric]
intro x
intro y
rw [R_even]
intro h
rw [R_even]
rw [add_comm]
exact h
done


theorem R_even_is_transitive : Transitive R_even := by
rw [Transitive]
intro x
intro y
intro z
rw [R_even]
rw [R_even]
rw [R_even]
intro hxy hyz
rw [Int.even_add] at hxy
rw [Int.even_add]
rw [hxy]
rw [← Int.even_add]
exact hyz
done


--alternative exericse 4.1.
theorem R_sq_is_reflexive : ∀x : ℤ,  Even (x^2 + x^2) := by
intro x
rw [← two_mul]
apply even_two_mul
done


theorem R_sq_is_symmetric : ∀ x y : ℤ, Even (x^2 + y^2) → Even (y^2 + x^2) := by
intro x
intro y
intro h
rw [add_comm]
exact h
done


theorem R_sq_is_transitive : ∀ x y z : ℤ, (Even (x^2 + y^2) ∧ Even (y^2 + z^2)) → Even (x^2 + z^2) := by
intro x
intro y
intro z
intro h
cases' h with hxy hyz
rw [Int.even_add] at hxy
rw [Int.even_add]
rw [hxy]
rw [← Int.even_add]
exact hyz
done



--exercise 4.2.
--We will do this on paper.



--exercise 4.3.
def f : (ℤ × ℤ) → (ℤ × ℤ) := λ (m, n) ↦ (m + n, 2*m + n)

example : f (2, 3)  = (5, 7) := by
rfl
done


theorem f_is_injective : Injective f := by
intro x
intro y
intro h
cases' x with m n
cases' y with m' n'
simp [f] at h
cases' h with h1 h2
rw [two_mul] at h2
rw [two_mul] at h2
rw [add_assoc] at h2
rw [add_assoc] at h2
rw [h1] at h2
rw [add_right_cancel_iff] at h2
rw [h2] at h1
rw [add_left_cancel_iff] at h1
rw [h1]
rw [h2]
done


theorem f_is_surjective : Surjective f := by
intro x
cases' x with x y
simp [f]
use (y - x)
use 2*x - y
constructor
ring
ring
done


theorem f_is_bijective : Bijective f := by
rw [Bijective]
constructor
apply f_is_injective
apply f_is_surjective
done



--exercise 4.4.1
def f_4_4_1 : ℝ → ℝ := λ x ↦ x^2 + 3


example : f_4_4_1 '' Icc 3 5 = Icc 12 28 := by
apply Set.ext
intro x
constructor
intro h
cases' h with y hy
cases' hy with hy1 hy2
simp [f_4_4_1] at hy2
cases' hy1 with hyb hyt
rw [mem_Icc]
constructor
rw [← hy2]
nlinarith
rw [← hy2]
nlinarith
intro h
use (sqrt (x - 3))
constructor
rw [mem_Icc]
rw [mem_Icc] at h
cases' h with h1 h2
constructor
rw [le_sqrt']
nlinarith
linarith
rw [sqrt_le_left]
nlinarith
linarith
simp [f_4_4_1]
rw [sq_sqrt]
norm_num
rw [mem_Icc] at h
nlinarith
done


--exercise 4.4.2
section

variable (A B : Type)
variable (X Y : Set A)
variable (g : A → B)

example : g '' (X ∩ Y) ⊆ g '' X ∩ g '' Y := by
intro b
intro h
cases' h with a ha
cases' ha with ha1 ha2
cases' ha1 with hax hay
constructor
use a
use a
done


--exercise 4.4.3
--we will do this on paper.
end



--exercise 4.5.1
--Set_option class.instance_max_depth 100

noncomputable def f_4_5_1_bounded : ℝ → ℝ :=
λ x ↦ sqrt 2 + exp x

def codomain_f_4_5_1_bounded' : Set ℝ := {y | sqrt 2 < y}


theorem f_4_5_1_is_injective : Injective f_4_5_1_bounded := by
rw [Injective]
intro x
intro y
intro h
rw [f_4_5_1_bounded] at h
rw [f_4_5_1_bounded] at h
rw [add_left_cancel_iff] at h
rw [exp_eq_exp] at h
exact h
done


theorem f_4_5_1_is_surjective /-(h: 0 < f_4_5_1 x - sqrt 2)-/: Surjective f_4_5_1_bounded := by
rw [Surjective]
intro y
use Real.log (y - Real.sqrt 2)
simp [f_4_5_1_bounded]
rw [Real.exp_log]
ring
sorry
done


theorem f_4_5_1_is_bijective : Bijective f_4_5_1_bounded := by
rw [Bijective]
constructor
apply f_4_5_1_is_injective
apply f_4_5_1_is_surjective
done



--exercise 4.5.2
def set_A : Set (ℕ × ℕ) := { mn | mn.1 ≤ mn.2 }


def f_4_5_2 : set_A  → ℕ × ℕ := λ mn ↦ (mn.val.2, mn.val.1)


theorem f_4_5_2_is_injective : Injective f_4_5_2 := by
rw [Injective]
intro x
intro y
intro h
cases' x.val with m n
cases' y.val with m' n'
simp [f_4_5_2] at h
rw [and_comm] at h
rw [← Prod.eq_iff_fst_eq_snd_eq] at h
exact SetCoe.ext h
done

theorem f_4_5_2_is_surjective : Surjective f_4_5_2 := by
rw [Surjective]
intro x
cases' x with m n
use {val := (n, m), property := sorry}
simp [f_4_5_2]
done

theorem f_4_5_2_is_bijective : Bijective f_4_5_2 := by
rw [Bijective]
constructor
apply f_4_5_2_is_injective
apply f_4_5_2_is_surjective
done



--exercise 4.6
theorem comp_is_bijective : ∀ {X Y Z : Type} (f : X → Y) (g : Y → Z), Bijective f → Bijective g → Bijective (g ∘ f) := by
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
rw [hx]
rw [hy]
done


def R_card (X Y : Type) : Prop := ∃ f : X → Y, Bijective f

theorem R_card_is_reflexive : Reflexive R_card := by
rw [Reflexive]
intro X
rw [R_card]
use id
rw [Bijective]
constructor
rw [Injective]
intro x
intro y
intro h
exact h
rw [Surjective]
intro y
use y
rw [id]
done


theorem R_card_is_symmetric : Symmetric R_card := by
rw [Symmetric]
intro X
intro Y
intro h
cases' h with f hf
rw [R_card]
have h2 : Bijective f
exact hf
rw [bijective_iff_has_inverse] at hf
cases' hf with g hg
have h3 : Bijective g := by
  rw [bijective_iff_has_inverse]
  use f
  cases' hg with hg1 hg2
  constructor
  rw [Function.RightInverse] at hg2
  exact hg2
  rw [Function.RightInverse]
  exact hg1
use g
done


theorem R_card_is_transitive : Transitive R_card := by
rw [Transitive]
intro X
intro Y
intro Z
intro hXY
intro hYZ
cases' hXY with f hf
cases' hYZ with g hg
rw [R_card]
use g ∘ f
exact comp_is_bijective f g hf hg
done
