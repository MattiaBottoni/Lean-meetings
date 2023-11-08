import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function

open Set
open Function

--exericse 4.1.
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
section

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

end
