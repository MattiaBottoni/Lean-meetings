import Mathlib.Tactic


/-We will use P, Q and R as our variables. In our case, the variables are statements (Prop)
which are either true or false.-/


variable (P Q R : Prop)

--intro, exact and apply--------------------------------------------------------------------

/-One of the most important tactic is "intro". You can use that if you have an implication
in your goal (what you want to prove) and would like to have the left side of the implication
as a hypothesis.
If you have a hypothesis that looks exactly as your goal, you can use the "exact" tactic to
prove the statement.
If your hypothesis is an implication and your goal looks like the righthand side of the
implication, use the "apply" tactic to change the goal to the lefthand side of the implication.
Click through each line of the proof and see what happens for yourself.
-/

example :  P → P := by
intro h
exact h
done

example :  P → P := by--Try it yourself! Delete the sorry, command first.
sorry
done

example: P → (P → Q) → Q:= by
intro hP
intro hpq
apply hpq --here you have to use apply to change the goal to P
exact hP
done

example: P → (P → Q) → Q:= by--Try it yourself! Delete the sorry, command first.
sorry
done

--split, left/right and cases--------------------------------------------------------------

/-You all saw the ∧ (and) and ∨ (or) symbols in the lecture. There are two different cases
to consider: once, when ∧ or ∨ are in the goal and once when they are in a hypothesis.
When they are in the goal, use the "split" tactic for ∧ and the "left" or "right" tactic for
∨. The "split" tactic will give you two goals where you have to prove the left side first and
then the right side. With the "left" or "right" tactic you decide which part you want to prove!
Do you understand why this is so? Think about the logical definitions of ∧ and ∨.
When ∧ and ∨ are in the hypothesis, you always use the "cases" tactic. This time, the ∧ is the
simpler case, as you still have to prove the same statement, but now with two hypotheses. If
on the other hand, your hypothesis had an ∨, you will have to prove the same goal twice. Once 
with the lefthand part of the hypothesis and once with the righthand side.
Again, do you understand why? -/

example : P → Q → (P ∧ Q) := by
intro hp
intro hq
constructor
exact hp
exact hq
done

example : P → Q → (P ∧ Q) := by --Try it yourself!
sorry
done

example : (P ∧ Q) → P := by
intro hpq
rcases hpq with ⟨hp, hq⟩  
exact hp
done

example : (P ∧ Q) → P := by --Try it yourself!
sorry
done

example : P → (P ∨ Q) := by
intro hp
left
exact hp
done

example : P → (P ∨ Q) := by --Try it yourself!
sorry
done 

example : Q → (P ∨ Q) := by
intro hq
right
exact hq
done

example : Q → (P ∨ Q) := by --Try it yourself!
sorry
done

example : (P ∨ Q) → (Q ∨ P) := by
intro hpq
rcases hpq with hp | hq 
right
exact hp
left
exact hq
done

example : (P ∨ Q) → (Q ∨ P) := by--Try it yourself!
sorry
done

/-keep in mind: ∧ is easy as an hypothesis, but not so easy to prove. 
                 ∨ is easy as to prove, but not so easy as an hypothesis.-/

--by_contra and by_cases--------------------------------------------------------------------

example : P  → (¬P) →  Q := by
intro hp
intro hnp
by_contra hnq
apply hnp
exact hp
done

example : P  → (¬P) →  Q := by --Try it yourself!
sorry
done

example : (Q ∨ ¬Q) := by
by_cases hq : Q --you can also just use by_cases Q, but then the hypothesis is called h.
left
exact hq
right
exact hq
done

example : (Q ∨ ¬Q) := by --Try it yourself!
sorry
done

--Exercises from the exercises sheet 0 and 1------------------------------------------------

--sheet 0 exercise 5.1.
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by --this is doable
constructor --split used here for the first time
intro hpqr --intro used here for the first time
rcases hpqr with ⟨ hp, hqr ⟩ --cases used here for the first time
rcases hqr with hq | hr
left --left used here for the first time
constructor
exact hp --exact used here for the first time
exact hq
right --right used here for the first time
constructor
exact hp
exact hr
intro h
rcases h with hpq | hpr
rcases hpq with ⟨ hp, hq ⟩ 
constructor
exact hp
left
exact hq
rcases hpr with ⟨ hp, hr ⟩
constructor
exact hp
right
exact hr
done


--sheet 0 exercise 5.2.
example : (P → Q) ↔ (¬Q → ¬P) := by
constructor
intro h
intro hnq
intro hp
apply hnq --apply used here for the first time
apply h
exact hp
intro h
intro hp
by_contra hnq --by_contra used here for the first time
apply h
exact hnq
exact hp
done


--sheet 1 exercise 6.1.
example : (P ↔ ¬Q) ↔ (¬P → Q) ∧ (Q → ¬P) := by
constructor
intro h
rcases h with ⟨ hpq, hqp ⟩ 
constructor
intro hnp
by_contra hnq
apply hnp
apply hqp
exact hnq
intro hq
intro hp
apply hpq
exact hp
exact hq
intro h
rcases h with ⟨ hpq,  hqp ⟩
constructor
intro hp
intro hq
apply hqp
exact hq
exact hp
intro hnq
by_contra hnp
apply hnq
apply hpq
exact hnp
done


--sheet 1 exercise 6.2.
example : ¬P → Q ↔ (¬P ∧ ¬Q) → Q ∧ ¬Q := by
constructor
intro h
intro h2
rcases h2 with ⟨ hnp, hnq ⟩
constructor
apply h
exact hnp
exact hnq
intro h
intro hnp
by_contra hnq
have h2 : (Q ∧ ¬Q) → False
intro hweird
rcases hweird with ⟨ hq, hnq2 ⟩ 
apply hnq
exact hq
apply h2
apply h
constructor
exact hnp
exact hnq
done

--sheet 1 exercise 7.1.
example : (P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ↔ P := by
constructor
intro h
rcases h with h1 | h2
rcases h1 with ⟨ h_left,  h_right ⟩ 
exact h_left
rcases h2 with ⟨ h_left,  h_right ⟩
exact h_left
intro hp
by_cases Q --by_cases used here for the first time. this was the missing piece to solve this exercise!
right
constructor
exact hp
exact h
left
constructor
exact hp
intro h2
rcases h2 with hnp | hq 
apply hnp
exact hp
apply h
exact hq
done

--sheet 1 exercise 7.2.
example : (¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ↔ ¬P := by
constructor
intro h
rcases h with h1 | h2 
intro hp
apply h1
left
exact hp
rcases h2 with ⟨ hnp, hnq⟩ 
exact hnp
intro hnp
by_cases Q
left
intro h2
rcases h2 with h_left | h_right
apply hnp
exact h_left
apply h_right
exact h
right
constructor
exact hnp
exact h
done

--I will also include the deMorgan laws, even though they are not part of the exercise sheets.

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by --this is doable
constructor
intro h
constructor
intro hp
apply h
left
exact hp
intro hq
apply h
right
exact hq
intro h
rcases h with ⟨hnp, hnq⟩ 
intro h2
rcases h2 with h_left | h_right
apply hnp
exact h_left
apply hnq
exact h_right
done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
constructor
intro hnpq
by_cases Q
left
intro hp
apply hnpq
constructor
exact hp
exact h
right
exact h
intro h
intro hpq
rcases hpq with ⟨hp, hq⟩ 
rcases h with hnp | hnq
apply hnp
exact hp
apply hnq
exact hq
done            