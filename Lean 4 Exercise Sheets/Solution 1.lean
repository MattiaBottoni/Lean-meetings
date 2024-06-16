import Mathlib.Tactic

/-We will use P, Q and R as our variables. In our case, the variables are statements (Prop)
which are either true or false.-/

variable (P Q R : Prop)

open Classical  --Did is only used for the proofs that do not rely on tactics.


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
example :  P → P := by
intro h
exact h
done

/-For Level 1 only, I will add the proof of each statement without using tactics. Thank you Marius Furter for
your support in this-/
example :  P → P := fun p : P => p


--Show that P ⇒ (P ⇒ Q) ⇒ Q.
example: P → (P → Q) → Q:= by
intro hP
intro hpq
apply hpq --here you have to use apply to change the goal to P
exact hP
done

example: P → (P → Q) → Q:= fun p : P => fun h : P → Q => h p

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
example : P → Q → (P ∧ Q) := by
intro hp
intro hq
constructor
exact hp
exact hq
done

example : P → Q → (P ∧ Q) := fun p : P => fun q : Q => And.intro p q


--Show that (P ∧ Q) ⇒ P.
example : (P ∧ Q) → P := by
intro hpq
cases' hpq with hp hq
exact hp
done

example : (P ∧ Q) → P := fun pq : P ∧ Q => And.left pq


--Show that P ⇒ (P ∨ Q).
example : P → (P ∨ Q) := by
intro hp
left
exact hp
done

example : P → (P ∨ Q) := fun p : P => Or.inl p


--Show that Q ⇒ (P ∨ Q).
example : Q → (P ∨ Q) := by
intro hq
right
exact hq
done

example : Q → (P ∨ Q) := fun q : Q => Or.inr q


--Show that (P ∨ Q) ⇒ (Q ∨ P).
example : (P ∨ Q) → (Q ∨ P) := by
intro hpq
cases' hpq with hp hq
right
exact hp
left
exact hq
done

example : (P ∨ Q) → (Q ∨ P) := fun pq : P ∨ Q => pq.elim Or.inr Or.inl

/-keep in mind: ∧ is easy as a hypothesis, but not so easy to prove.
                 ∨ is easy to prove, but not so easy as a hypothesis.-/


--by_contra and by_cases--------------------------------------------------------------------

/-sometimes it is a good thing to assume that a statement is wrong and then to prove that this results into
False. To do this, you can use the "by_contra" tactic. If, on the other hand, you want to have two cases of
the same hypothesis, namely that once it is True and once False (e.g h : x > 0 and ¬x > 0) you can use the
"by_cases" tactic.-/

--Show that P ⇒ (¬P) ⇒ Q.
example : P  → (¬P) →  Q := by
intro hp
intro hnp
by_contra hnq
apply hnp
exact hp
done

example : P  → (¬P) →  Q := fun p : P => fun np : ¬P => False.elim (np p)


--Show that (Q ∨ ¬Q).
example : (Q ∨ ¬Q) := by
by_cases hq : Q --you can also just use by_cases Q, but then the hypothesis is called h.
left
exact hq
right
exact hq
done

example : (Q ∨ ¬Q) := Classical.em Q --here we use the excluded middle principle, which is not constructive!


--Exercises from exercise sheets 0 and 1------------------------------------------------

/-Sheet 0 and 1 were summarized in on level. This is because only a few exercises from both sheets
make sense to be implemented in Lean. From sheet 0 we look at exercise 5 and from sheet 1 we look at
6 and 7. And the end of this level, I also added both deMorgan laws, as they fit well into this level. -/

--sheet 0 exercise 0.5.1.
/-Show the following statements are always true, no matter what truth values of P, Q, R are.
Such statements are called ”tautologies”.
(Distributive Law). P ∧ (Q ∨ R) ⇐⇒ (P ∧ Q) ∨ (P ∧ R).-/
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
constructor --constructor used here for the first time
intro hpqr --intro used here for the first time
cases' hpqr with hp hqr --cases' used here for the first time
cases' hqr with hq hr
left --left used here for the first time
constructor
exact hp --exact used here for the first time
exact hq
right --right used here for the first time
constructor
exact hp
exact hr
intro h
cases' h with hpq hpr
cases' hpq with hp hq
constructor
exact hp
left
exact hq
cases' hpr with hp hr
constructor
exact hp
right
exact hr
done

example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := Iff.intro
    (fun h : P ∧ (Q ∨ R) =>
      have p : P := And.left h
      have qr : Q ∨ R := And.right h
      Or.elim qr
        (fun q : Q => Or.inl (And.intro p q))
        (fun r : R => Or.inr (And.intro p r))
    )
    (fun h : (P ∧ Q) ∨ (P ∧ R) =>
      Or.elim h
      (fun hl : P ∧ Q =>
        have p : P := And.left hl
        have q : Q := And.right hl
        And.intro p (Or.inl q))
      (fun hr : P ∧ R =>
        have p : P := And.left hr
        have r : R := And.right hr
        And.intro p (Or.inr r))
      )


--sheet 0 exercise 0.5.2.
/-(Contrapositive). (P ⇒ Q) ⇔ (¬Q ⇒ ¬P).-/
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

example : (P → Q) ↔ (¬Q → ¬P) := Iff.intro
    (fun h : P → Q =>
      fun hnq : ¬Q =>
        fun hp : P =>
          have q : Q := h hp
          show False from hnq q
    )
    (fun h : ¬Q → ¬P =>
      fun hp : P =>
        byContradiction (fun nq : ¬Q => h nq hp)
    )



--sheet 1 exercise 1.6.1.
/-Show the following statements are logically equivalent.
(P ⇔ ¬Q) ⇔ ((¬P ⇒ Q) ∧ (Q ⇒ ¬P)).-/
example : (P ↔ ¬Q) ↔ (¬P → Q) ∧ (Q → ¬P) := by
constructor
intro h
cases' h with hpq hqp
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
cases' h with hpq hqp
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

example : (P ↔ ¬Q) ↔ (¬P → Q) ∧ (Q → ¬P) := Iff.intro
    (fun h : P ↔ ¬Q =>
      have hpnq : P → ¬Q := Iff.mp h
      have hnqp : ¬Q → P := Iff.mpr h
      And.intro
        (fun hnp : ¬P =>
          byContradiction (fun hnq : ¬Q => hnp (hnqp hnq)))
        (fun hq : Q =>
          fun hnp : P =>
            have hnq : ¬Q := hpnq hnp
            show False from hnq hq)
    )
    (fun h : (¬P → Q) ∧ (Q → ¬P) =>
      have hnpq : ¬P → Q := And.left h
      have hqnp : Q → ¬P := And.right h
      Iff.intro
        (fun hp : P =>
          fun hq : Q =>
          have hnp : ¬P := hqnp hq
          hnp hp)
        (fun hnq : ¬Q =>
          byContradiction (fun hnp : ¬P => hnq (hnpq hnp)))
    )


--sheet 1 exercise 1.6.2.
/-¬P ⇒ Q = (¬P ∧ ¬Q) ⇒ Q ∧ ¬Q-/
example : ¬P → Q ↔ (¬P ∧ ¬Q) → Q ∧ ¬Q := by
constructor
intro h
intro h2
cases' h2 with hnp hnq
constructor
apply h
exact hnp
exact hnq
intro h
intro hnp
by_contra hnq
have h2 : (Q ∧ ¬Q) → False
intro hweird
cases' hweird with hq hnq2
apply hnq
exact hq
apply h2
apply h
constructor
exact hnp
exact hnq
done

example : ¬P → Q ↔ (¬P ∧ ¬Q) → Q ∧ ¬Q := Iff.intro
    (fun h : ¬P → Q =>
      fun h2 : ¬P ∧ ¬Q =>
        have hnp : ¬P := And.left h2
        have hnq : ¬Q := And.right h2
        And.intro
          (h hnp)
          hnq
    )
    (fun h : (¬P ∧ ¬Q) → Q ∧ ¬Q =>
      fun hnp : ¬P =>
        byContradiction (fun hnq : ¬Q =>
        have hnPnQ : ¬P ∧ ¬Q := And.intro hnp hnq
        have h2 : Q ∧ ¬Q := h hnPnQ
        show False from h2.right h2.left)
    )



--sheet 1 exercise 1.7.1.
/-Use the laws of logical equivalences (Commutative laws, associative laws, etc.) to verify the following logical equivalences.
(P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ⇔ P-/
example : (P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ↔ P := by
constructor
intro h
cases' h with h1 h2
cases' h1 with h_left h_right
exact h_left
cases' h2 with h_left h_right
exact h_left
intro hp
by_cases hq : Q --by_cases used here for the first time.
right
constructor
exact hp
exact hq
left
constructor
exact hp
intro h2
cases' h2 with hnp hq2
apply hnp
exact hp
apply hq
exact hq2
done

example : (P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ↔ P := Iff.intro
    (fun h : (P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) =>
      Or.elim h
      (fun h1 : P ∧ (¬(¬P ∨ Q)) =>
        And.left h1)
      (fun h2 : P ∧ Q =>
        And.left h2)
    )
    (fun hp : P =>
      have hq : Q ∨ ¬Q := Classical.em Q
      Or.elim hq
      (fun hq : Q =>
        Or.inr (And.intro hp hq))
      (fun hnq : ¬Q =>
        Or.inl (And.intro hp (fun hnpq : ¬P ∨ Q =>
                                Or.elim hnpq
                                  (fun hnp : ¬P =>
                                  show False from hnp hp)
                                  (fun hq : Q =>
                                  show False from hnq hq))))
    )


--sheet 1 exercise 1.7.2.
/-(¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ⇔ ¬P-/
example : (¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ↔ ¬P := by
constructor
intro h
cases' h with h1 h2
intro hp
apply h1
left
exact hp
cases' h2 with hnp hnq
exact hnp
intro hnp
by_cases hq : Q
left
intro h2
cases' h2 with h_left h_right
apply hnp
exact h_left
apply h_right
exact hq
right
constructor
exact hnp
exact hq
done

example : (¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ↔ ¬P := Iff.intro
    (fun h : (¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) =>
      Or.elim h
      (fun h1 : ¬(P ∨ ¬Q) =>
        fun hp : P =>
          show False from h1 (Or.inl hp))
      (fun h2 : ¬P ∧ ¬Q =>
        And.left h2)
    )
    (fun hnp : ¬P =>
      have hq : Q ∨ ¬Q := Classical.em Q
      Or.elim hq
        (fun hq : Q =>
          Or.inl (fun h : P ∨ ¬Q =>
                  Or.elim h
                    (fun h1 : P =>
                      show False from hnp h1)
                    (fun h2 : ¬Q =>
                      show False from h2 hq))
        )
        (fun hq : ¬Q =>
          Or.inr (And.intro hnp hq))
      )



--I will also include the deMorgan laws, even though they are not part of the exercise sheets.

--Show that ¬(P ∨ Q) ⇔ ((¬P) ∧ (¬Q)).
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
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
cases' h with hnp hnq
intro h2
cases' h2 with h_left h_right
apply hnp
exact h_left
apply hnq
exact h_right
done

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := Iff.intro
    (fun h : ¬(P ∨ Q) =>
      And.intro
        (fun hp : P =>
          show False from h (Or.inl hp))
        (fun hq : Q =>
          show False from h (Or.inr hq))
    )
    (fun h : ¬P ∧ ¬Q =>
      fun h2 : P ∨ Q =>
        Or.elim h2
        (fun hp : P =>
          show False from h.left hp)
        (fun hq : Q =>
          show False from h.right hq)
    )


--Show that ¬(P ∧ Q) ⇔ ((¬P) ∨ (¬Q)).
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
constructor
intro hnpq
by_cases hq : Q
left
intro hp
apply hnpq
constructor
exact hp
exact hq
right
exact hq
intro h
intro hpq
cases' hpq with hp hq
cases' h with hnp hnq
apply hnp
exact hp
apply hnq
exact hq
done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := Iff.intro
    (fun h : ¬(P ∧ Q) =>
      have hq : Q ∨ ¬Q := Classical.em Q
      Or.elim hq
        (fun hq : Q =>
          Or.inl (fun hnp : P =>
                  show False from h (And.intro hnp hq)))
        (fun hnq : ¬Q =>
          Or.inr hnq))
    (fun h : ¬P ∨ ¬Q =>
      fun hpq : P ∧ Q =>
        Or.elim h
        (fun hnp : ¬P =>
          show False from hnp hpq.left)
        (fun hnq : ¬Q =>
          show False from hnq hpq.right))
