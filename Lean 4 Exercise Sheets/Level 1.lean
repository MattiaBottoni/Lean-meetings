import Mathlib.Tactic


/-We will use P, Q and R as our variables. In our case, the variables are statements (Prop)
which are either true or false.-/

variable (P Q R : Prop)

/-I always give some hints for the exercises. If, at a later time, you want to solve the exercises all on your own, simply delete my green hints.-/


--intro, exact and apply--------------------------------------------------------------------

/-One of the most important tactics is "intro". You can use that if you have an implication
in your goal "⊢" (what you want to prove) and would like to have the left side of the
implication as a hypothesis.
If you have a hypothesis that looks exactly like your goal, you can use the "exact" tactic to
prove the statement.
If your hypothesis is an implication and your goal looks like the righthand side of that
implication, use the "apply" tactic to change the goal to the lefthand side of the implication.
Click through each line of the proof and see what happens for yourself.
-/

--Show that P ⇒ P.
example :  P → P := by --Try it yourself! Delete the sorry command first.
sorry
done


--Show that P ⇒ (P ⇒ Q) ⇒ Q.
example: P → (P → Q) → Q:= by --At some point, you will have a hypothesis h2 : P → Q. Then you will need to use apply h2.
sorry
done


--constructor, left/right and rcases--------------------------------------------------------------

/-You all saw the ∧ (and) and ∨ (or) symbols in the lecture. There are two different cases
to consider: once, when ∧ or ∨ are in the goal and once when they are in a hypothesis.
When they are in the goal, use the "constructor" tactic for ∧ and the "left" or "right"
tactic for ∨. The "constructor" tactic will give you two goals where you have to prove the left
side first and then the right side. With the "left" or "right" tactic you decide which part you
want to prove! Do you understand why this is so? Think about the logical definitions of ∧ and ∨.
When ∧ and ∨ are in the hypothesis, you always use the "cases'" tactic. This time, the ∧ is the
simpler case, as you still have to prove the same statement, but now with two hypotheses. If,
on the other hand, your hypothesis had an ∨, you will have to prove the same goal twice. Once
with the lefthand part of the hypothesis and once with the righthand side.
Again, do you understand why? -/

--Show that P ⇒ Q ⇒ (P ∧ Q).
example : P → Q → (P ∧ Q) := by --Here, ∧ is in the goal.
sorry
done


--Show that (P ∧ Q) ⇒ P.
example : (P ∧ Q) → P := by --Here, ∧ is in the hypothesis. So you use "cases' h with h1 h2"
sorry
done


--Show that P ⇒ (P ∨ Q).
example : P → (P ∨ Q) := by --Here, ∨ is in the goal.
sorry
done


--Show that Q ⇒ (P ∨ Q).
example : Q → (P ∨ Q) := by --Here, ∨ is in the goal again. But on the other side.
sorry
done


--Show that (P ∨ Q) ⇒ (Q ∨ P).
example : (P ∨ Q) → (Q ∨ P) := by --Here, ∨ is in the hypothesis. You "cases'" again. Think about when you want to use "left" and when you want to use "right".
sorry
done

/-keep in mind: ∧ is easy as a hypothesis, but not so easy to prove.
                 ∨ is easy to prove, but not so easy as a hypothesis.-/


--by_contra and by_cases--------------------------------------------------------------------

/-sometimes it is a good thing to assume that a statement is wrong and then to prove that this results into
False. To do this, you can use the "by_contra" tactic. If, on the other hand, you want to have two cases of
the same hypothesis, namely that once it is True and once False (e.g h : x > 0 and ¬x > 0) you can use the
"by_cases" tactic.-/

--Show that P ⇒ (¬P) ⇒ Q.
example : P  → (¬P) →  Q := by --When using "by_contra", write "by_contra hnp" to give your new hypothesis a certain name. Keep in mind that ¬Q is the same as Q → False. So you can use apply h, if your hypothesis is ¬Q and your goal is False.
sorry
done


--Show that (Q ∨ ¬Q).
example : (Q ∨ ¬Q) := by --When using "by_cases", you always have to say what you want to case (e.g. Q or x = 1). You can also give your hypothesis a name, try "by_cases h : Q".
sorry
done


--Exercises from exercise sheets 0 and 1------------------------------------------------

/-Sheet 0 and 1 were summarized in on level. This is because only a few exercises from both sheets
make sense to be implemented in Lean. From sheet 0 we look at exercise 5 and from sheet 1 we look at
6 and 7. And the end of this level, I also added both deMorgan laws, as they fit well into this level. -/

--sheet 0 exercise 0.5.1.
/-Show the following statements are always true, no matter what truth values of P, Q, R are.
Such statements are called ”tautologies”.
(Distributive Law). P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R).-/
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by --You don't need "by_contra" or "by_cases" here. All you have to do is to keep a cool head in all the cases. To change a ↔ into two →, use "constructor".
sorry
done


--sheet 0 exercise 0.5.2.
/-(Contrapositive). (P ⇒ Q) ⇔ (¬Q ⇒ ¬P).-/
example : (P → Q) ↔ (¬Q → ¬P) := by --Here you will need "by_contra" in the second goal after your goal is only Q.
sorry
done



--sheet 1 exercise 1.6.1.
/-Show the following statements are logically equivalent.
(P ⇔ ¬Q) ⇔ ((¬P ⇒ Q) ∧ (Q ⇒ ¬P)).-/
example : (P ↔ ¬Q) ↔ (¬P → Q) ∧ (Q → ¬P) := by --Again, you will need to use "by_contra" here sometimes.
sorry
done


--sheet 1 exercise 1.6.2.
/-¬P ⇒ Q = (¬P ∧ ¬Q) ⇒ Q ∧ ¬Q-/
example : ¬P → Q ↔ (¬P ∧ ¬Q) → Q ∧ ¬Q := by --For the second implication, after your goal is Q, use "by_contra" and then use "have h2 : (Q ∧ ¬Q) → False". You will then need to prove this and then you will have h2 as a new hypothesis. You can always add hypothesis like this, if you can prove them.
sorry
done



--sheet 1 exercise 1.7.1.
/-Use the laws of logical equivalences (Commutative laws, associative laws, etc.) to verify the following logical equivalences.
(P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ⇔ P-/
example : (P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ↔ P := by --This is a bit tricky. In the second implication, your only hypothesis is h : P. Use "by_cases hq : Q" to get two goals.
sorry
done


--sheet 1 exercise 1.7.2.
/-(¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ⇔ ¬P-/
example : (¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ↔ ¬P := by --In this execises you will also need a "by_cases hq : Q" in the second implication, right after you intro hnp.
sorry
done


--I will also include the deMorgan laws, even though they are not part of the exercise sheets.

--Show that ¬(P ∨ Q) ⇔ ((¬P) ∧ (¬Q)).
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by --This deMorgan law is pretty easy. You won't need any "by_contra" or "by_cases"
sorry
done


--Show that ¬(P ∧ Q) ⇔ ((¬P) ∨ (¬Q)).
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by --This is a bit more difficult. Use a "by_cases hq : Q" in the first implication right after you intro hnpq
sorry
done
