import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-In order to manipulate equations in Lean (which you will need to do in exercise 2.1),
you need to know a lot of algebra tactics. I will show you here how to they are used, but I also
wrote a cheat sheet were they are all on. So if you prefer to directly solve exercise 2.1,
you can skip the next section.-/

section
variable (a b c : ℝ)


example :  (a - b = 0) ↔ (a = b) := by --Have a look at the cheat sheet to find the proper rewrite (rw). Don't forget that you can (and must) use tacticts from level 1. With "rw [] at h", you can rewrite a hypothesis.
sorry
done


example : (a - b - c = 5) ↔ (a - (b + c) = 5) := by --If you want to use a rw tactic backwards, write "rw [← blabla]". You can write "←" by typing "\l"
sorry
done


example : (a + b = 5) ↔ (b + a = 5) := by --Up to a certain example, you will just need "constructor", "intro" and "exact" from level 1.
sorry
done


example : (a + b - c = 5) ↔ (a + (b - c) = 5) := by --Notice that you can always decide if you want to rewrite the hypothesis or the goal. Depending on how they look, you will need "←".
sorry
done


example : (a^2 - b^2 = 5) ↔ ((a+b)*(a-b) = 5) := by
sorry
done


example : (a - b = 5) ↔ (a + -b = 5) := by
sorry
done


example : (a + b + c = 5) ↔ (a + (b + c) = 5) := by
sorry
done


example : (a + b + c = 5) ↔ (a + c + b = 5) := by
sorry
done


example : (a - b + c = 5) ↔ (a - (b - c) = 5) := by
sorry
done


example : (a * (b - c) = 5) ↔ (a * b - a * c = 5) := by
sorry
done


example : ((a - b) * c = 5) ↔ (a * c - b * c = 5) := by
sorry
done


example : (a * b = 0) ↔ (a = 0 ∨ b = 0) := by --This last one is a bit more advanced. You will have to use "cases'" and "left/right" here.
sorry
end


--Exercises from exercise sheet 2-----------------------------------------------------------

section --here I use section, because the variables I use here should only be used in this exercise. This does not need to bother you.
  variable {α β : Type _}
  variable (I J : Set α)
  variable (A : α → Set β)
  open Set


  --exercise 2.1.2.
  example (h2 : J ⊆ I) : (⋃ j ∈ J, A j) ⊆ (⋃ i ∈ I, A i) := by --This exercise already contains a lot of new notation. Start with "intros x hx" (a way to introduce multiple things at once) and then use "simp" and "simp at hx" to change the goal and hypothesis in a more understandable way. When you will encounter a "∃" in the goal, use "use j" to fix this.
  sorry
  done


  --exercise 2.1.3.
  example (h2 : J ⊆ I) : (⋂ i ∈ I, A i) ⊆ (⋂ j ∈ J, A j) := by --Use "simp" right at the beginning. At some point you should have a hypotheis with a "∀". To deal with this use "specialize h x"
  sorry
  done
end



--exercise 2.2.1.
example (x y : ℝ) :  (x ^ 2 + 5 * y = y ^ 2 + 5 * x) → ((x = y) ∨ (x + y = 5)) := by --Have a look at the first three chapters of the repetition level. There you will find some helpful skills to solve this exercise.
sorry
done


--exercise 2.2.2.
example (a : ℤ) : (k * a^2 = 1* a) → ((a = -1) ∨ (a = 1) ∨ (a = 0)) := by --When you get stuck, use "apply?" to continue or have a look at the solutions. I did not know all these tactics and rewrites by heart and you don't need to too!
sorry
done


--exercise 2.2.3.
--We will do this one on paper.



--exercise 2.3.1.
example (x : ℝ) : (x ≤ -1) → (x ^ 3 - x) ≤ 0 := by --"linarith" and "nlinarith" are very useful here.
sorry
done


--exercise 2.3.2.
example (x y z : ℤ) : ((x ∣ y) ∨ (x ∣ z)) → (x ∣ y * z) := by --There are tactics here that solve this right-away. Use "exact?" to find them.
sorry
done



--exercise 2.4.
--we solve this one on paper.



--execise 2.5.1.
variable
  {X : Type _}
  (A B C : Set X)
  (x y z : X)

open Set


example (hc : y ∈ C): (A ×ˢ C) = (B ×ˢ C) → A = B := by --This proof is not so hard, but the new notations are a bit tricky. After you do "intro h", type "ext x". Now you will have to prove that x ∈ A ↔ x ∈ B. At two points you will have to use "have hx : (x,y) ∈ (A ×ˢ _)" where you will put C or B in the blank space.
sorry
done


--exercise 2.5.2.
example : 𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B) := by --Again this is just a bit tricky because we are working with powersets. But if you use "rw? at h" sometimes, you should be able to prove this.
sorry
done
