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
--here I do not define the relation beforehand. I just write the definition of the relation in the theorem statement.
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


example : image f_4_4_1 (Icc 3 5) = Icc 12 28 := by
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


example : preimage f_4_4_1 (Icc 12 19) = ((Icc 3 4) ∪ (Icc (-4) (-3))) := by
apply Set.ext
intro x
constructor
intro h
cases' h with hlb hub
simp [f_4_4_1] at hlb
simp [f_4_4_1] at hub
rw [mem_union]
simp_rw [← tsub_le_iff_right] at hlb
have h1 : (12 : ℝ)  - 3 = 9
norm_num
rw [h1] at hlb
rw [← le_sub_iff_add_le] at hub
have h2 : (19 : ℝ)  - 3 = 16
norm_num
rw [h2] at hub
by_cases hx : 0 ≤ x
rw [← Real.sqrt_le_left] at hlb
have h3 : sqrt 9 = 3
have h4 : (9 : ℝ)  = 3^2
norm_num
rw [h4]
rw [sqrt_sq]
norm_num
rw [h3] at hlb
left
rw [mem_Icc]
constructor
exact hlb
rw [← Real.le_sqrt] at hub
have h5 : sqrt 16 = 4
have h6 : (16 : ℝ)  = 4^2
norm_num
rw [h6]
rw [sqrt_sq]
norm_num
rw [h5] at hub
exact hub
exact hx
norm_num
exact hx
right
rw [mem_Icc]
constructor
rw [@not_le] at hx
rw [← neg_sq] at hub
rw [← Real.le_sqrt] at hub
have h5 : sqrt 16 = 4
have h6 : (16 : ℝ)  = 4^2
norm_num
rw [h6]
rw [sqrt_sq]
norm_num
rw [h5] at hub
rw [neg_le]
exact hub
linarith
norm_num
rw [@not_le] at hx
rw [← neg_sq] at hlb
rw [← Real.sqrt_le_left] at hlb
have h3 : sqrt 9 = 3
have h4 : (9 : ℝ)  = 3^2
norm_num
rw [h4]
rw [sqrt_sq]
norm_num
rw [h3] at hlb
rw [le_neg]
exact hlb
linarith
intro h
cases' h with h1 h2
cases' h1 with h1lb h1ub
simp [f_4_4_1]
constructor
nlinarith
nlinarith
simp [f_4_4_1]
rw [mem_Icc] at h2
constructor
nlinarith
nlinarith
done


--exercise 4.4.2
section

variable (A B : Type)
variable (X Y : Set A)
variable (g : A → B)


example : g '' (X ∩ Y) ⊆ g '' X ∩ g '' Y := by
intro y
intro h
cases' h with x hx
cases' hx with hx' hx''
cases' hx' with hX' hY'
constructor
use x
use x
done


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
def set_B : Set ℝ := {y | sqrt 2 < y}


noncomputable def f_4_5_1_bounded : ℝ → set_B :=
λ x ↦ {val := sqrt 2 + exp x, property := by simp [set_B] ;   exact exp_pos x}


theorem f_4_5_1_is_injective : Injective f_4_5_1_bounded := by
rw [Injective]
intro x
intro y
intro h
rw [f_4_5_1_bounded] at h
rw [f_4_5_1_bounded] at h
simp at *
exact h
done


theorem f_4_5_1_is_surjective : Surjective f_4_5_1_bounded := by
rw [Surjective]
intro y
cases' y with y hy
use Real.log (y - Real.sqrt 2)
simp [f_4_5_1_bounded]
rw [exp_log]
linarith
simp [set_B] at hy
linarith
done


theorem f_4_5_1_is_bijective : Bijective f_4_5_1_bounded := by
rw [Bijective]
constructor
apply f_4_5_1_is_injective
apply f_4_5_1_is_surjective
done


--exercise 4.5.2 --using cantor schroeder bernstein theorem
def set_A : Set (ℕ × ℕ) := { mn | mn.1 ≤ mn.2 }

def f_4_5_2a : set_A  → ℕ × ℕ := λ mn ↦ (mn.val.2, mn.val.1)

def f_4_5_2b :  ℕ × ℕ → set_A := λ (n,m) ↦ {val := (n,n + m), property := by simp [set_A]}


theorem f_4_5_2_a_is_injective : Injective f_4_5_2a := by
rw [Injective]
intro x
intro y
intro h
cases' x.val with m n
cases' y.val with m' n'
simp [f_4_5_2a] at h
rw [and_comm] at h
rw [← Prod.eq_iff_fst_eq_snd_eq] at h
exact SetCoe.ext h
done


theorem f_4_5_2_b_is_injective : Injective f_4_5_2b := by
rw [Injective]
intro x
intro y
intro h
cases' x with m n
cases' y with m' n'
simp [f_4_5_2b] at h
cases' h with h1 h2
rw [h1] at h2
rw [add_left_cancel_iff] at h2
rw [h1]
rw [h2]
done


theorem set_A_equi_NtimesN : ∃ h : set_A →  ℕ × ℕ, Bijective h := by
exact Embedding.schroeder_bernstein f_4_5_2_a_is_injective f_4_5_2_b_is_injective
done


--other approach for 4.5.2.
def set_A_N : (N : ℕ)  →  Set (ℕ × ℕ) := λN ↦ { mn | mn.1 ≤ mn.2 ∧  mn.2 ≤ N }


theorem set_A_N_is_finite : ∀ N : ℕ, Finite (set_A_N N) := by
sorry --we can see this as given.
done


theorem set_A_N_is_countable : ∀ N : ℕ, Countable (set_A_N N) := by
intro N
have h : Finite (set_A_N N)
exact set_A_N_is_finite N
apply Finite.to_countable
done


def set_union_A : Set (ℕ × ℕ) := ⋃ N : ℕ, set_A_N N


theorem set_union_A_is_countable : Countable set_union_A := by
rw [countable_coe_iff]
rw [set_union_A]
rw [Set.countable_iUnion_iff]
intro N
rw [← countable_coe_iff]
exact set_A_N_is_countable N
done


def set_B_in_A : Set (ℕ × ℕ) := {n | n.1 = n.2}


theorem set_B_in_A_is_infinite : Infinite set_B_in_A := by
sorry --we can see this as given.
done


theorem set_B_in_A_is_in_A : set_B_in_A ⊆ set_union_A := by
rw [subset_def]
intro x
intro h
rw [set_union_A]
rw [mem_iUnion]
rw [set_B_in_A] at h
cases' x with m n
use n
rw [set_A_N]
rw [mem_setOf] at h
rw [mem_setOf]
constructor
exact Nat.le_of_eq h
norm_num
done


theorem set_union_A_is_infinite : Infinite set_union_A := by
rw [← not_finite_iff_infinite]
intro h
have h2 : set_B_in_A ⊆ set_union_A := by
  exact set_B_in_A_is_in_A
have h3 : Finite set_B_in_A := by
  exact Finite.Set.subset set_union_A h2
have h4 : Infinite set_B_in_A := by
  exact set_B_in_A_is_infinite
rw [← not_finite_iff_infinite] at h4
exact h4 h3
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
