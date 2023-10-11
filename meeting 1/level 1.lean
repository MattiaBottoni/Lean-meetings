import tactic

/--We will use P, Q and R as our variables. In our case, the variables are statements (Prop)
which are either true or false.--/

variables (P Q R : Prop)

--intro, exact and apply--------------------------------------------------------------------

/--One of the most important tactic is "intro". You can use that if you have an implication
in your goal (what you want to prove) and would like to have the left side of the implication
as a hypothesis.
If you have a hypothesis that looks exactly as your goal, you can use the "exact" tactic to
prove the statement.
If your hypothesis is an implication and your goal looks like the righthand side of the
implication, use the "apply" tactic to change the goal to the lefthand side of the implication.
Click through each line of the proof and see what happens for yourself.
--/

example :  P → P :=
begin
intro h, 
exact h,
end

example :  P → P := --Try it yourself! Delete the sorry, command first.
begin
sorry,
end

example: P → (P → Q) → Q:=
begin
intro hP,
intro hpq,
apply hpq, --here you have to use apply to change the goal to P
exact hP,
end

example: P → (P → Q) → Q:= --Try it yourself! Delete the sorry, command first.
begin
sorry,
end

--split, left/right and cases--------------------------------------------------------------

/--You all saw the ∧ (and) and ∨ (or) symbols in the lecture. There are two different cases
to consider: once, when ∧ or ∨ are in the goal and once when they are in a hypothesis.
When they are in the goal, use the "split" tactic for ∧ and the "left" or "right" tactic for
∨. The "split" tactic will give you two goals where you have to prove the left side first and
then the right side. With the "left" or "right" tactic you decide which part you want to prove!
Do you understand why this is so? Think about the logical definitions of ∧ and ∨.
When ∧ and ∨ are in the hypothesis, you always use the "cases" tactic. This time, the ∧ is the
simpler case, as you still have to prove the same statement, but now with two hypotheses. If
on the other hand, your hypothesis had an ∨, you will have to prove the same goal twice. Once 
with the lefthand part of the hypothesis and once with the righthand side.
Again, do you understand why? --/

example : P → Q → (P ∧ Q) :=
begin
intro hp,
intro hq,
split,
exact hp,
exact hq,
end

example : P → Q → (P ∧ Q) := --Try it yourself!
begin
sorry,
end

example : (P ∧ Q) → P :=
begin
intro hpq,
cases hpq with hp hq,
exact hp,
end

example : (P ∧ Q) → P := --Try it yourself!
begin
sorry,
end

example : P → (P ∨ Q) :=
begin
intro hp,
left,
exact hp,
end 

example : P → (P ∨ Q) := --Try it yourself!
begin
sorry,
end 

example : Q → (P ∨ Q) :=
begin
intro hq,
right,
exact hq,
end

example : Q → (P ∨ Q) := --Try it yourself!
begin
sorry,
end

example : (P ∨ Q) → (Q ∨ P) :=
begin
intro hpq,
cases hpq with hp hq,
right,
exact hp,
left,
exact hq,
end

example : (P ∨ Q) → (Q ∨ P) := --Try it yourself!
begin
sorry,
end

/--keep in mind: ∧ is easy as an hypothesis, but not so easy to prove. 
                 ∨ is easy as to prove, but not so easy as an hypothesis.--/              

--by_contra and by_cases--------------------------------------------------------------------

example : P  → (¬P) →  Q :=
begin
intro hp,
intro hnp,
by_contra hnq,
apply hnp,
exact hp,
end

example : P  → (¬P) →  Q := --Try it yourself!
begin
sorry,
end

example : P → (Q ∨ ¬Q) :=
begin
intro hp,
by_cases hq : Q, --you can also just use by_cases Q, but then the hypothesis is called h.
left,
exact hq,
right,
exact hq,
end

example : P → (Q ∨ ¬Q) := --Try it yourself!
begin
sorry,
end

--Exercises from the exercises sheet 0 and 1------------------------------------------------

--sheet 0 exercise 5.1.
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := --this is doable
begin
split, --split used here for the first time
intro hpqr, --intro used here for the first time
cases hpqr with hp hqr, --cases used here for the first time
cases hqr with hq hr,
left, --left used here for the first time
split,
exact hp, --exact used here for the first time
exact hq,
right, --right used here for the first time
split,
exact hp,
exact hr,
intro h,
cases h with hpq hpr,
cases hpq with hp hq,
split,
exact hp,
left,
exact hq,
cases hpr with hp hr,
split,
exact hp,
right,
exact hr,
end


--sheet 0 exercise 5.2.
example : (P → Q) ↔ (¬Q → ¬P) :=
begin
split,
intro h,
intro hnq,
intro hp,
apply hnq, --apply used here for the first time
apply h,
exact hp,
intro h,
intro hp,
by_contra hnq, --by_contra used here for the first time
apply h,
exact hnq,
exact hp,
end


--sheet 1 exercise 6.1.
example : P ↔ ¬Q ↔ (¬P → Q) ∧ (Q → ¬P) :=
begin
split,
intro h,
cases h with hpq hqp,
split,
intro hnp,
by_contra hnq,
apply hnp,
apply hqp,
exact hnq,
intro hq,
intro hp,
apply hpq,
exact hp,
exact hq,
intro h,
cases h with hpq hqp,
split,
intro hp,
intro hq,
apply hqp,
exact hq,
exact hp,
intro hnq,
by_contra hnp,
apply hnq,
apply hpq,
exact hnp,
end


--sheet 1 exercise 6.2.
example : ¬P → Q ↔ (¬P ∧ ¬Q) → Q ∧ ¬Q :=
begin
split,
intro h,
intro h2,
cases h2 with hnp hnq,
split,
apply h,
exact hnp,
exact hnq,
intro h,
intro hnp,
by_contra hnq,
have h2 : (Q ∧ ¬Q) → false,
intro hweird,
cases hweird with hq hnq2,
apply hnq,
exact hq,
apply h2,
apply h,
split,
exact hnp,
exact hnq,
end

--sheet 1 exercise 7.1.
example : (P ∧ (¬(¬P ∨ Q))) ∨ (P ∧ Q) ↔ P :=
begin
split,
intro h,
cases h,
cases h,
exact h_left,
cases h,
exact h_left,
intro hp,
by_cases Q, --by_cases used here for the first time. this was the missing piece to solve this exercise!
right,
split,
exact hp,
exact h,
left,
split,
exact hp,
intro h2,
cases h2 with hnp hq,
apply hnp,
exact hp,
apply h,
exact hq,

end

--sheet 1 exercise 7.2.
example : (¬(P ∨ ¬Q)) ∨ (¬P ∧ ¬Q) ↔ ¬P :=
begin 
split,
intro h,
cases h,
intro hp,
apply h,
left,
exact hp,
cases h with hp hq,
exact hp,
intro hp,
by_cases Q,
left,
intro h2,
cases h2,
apply hp,
exact h2,
apply h2,
exact h,
right,
split,
exact hp,
exact h,
end

--I will also include the deMorgan laws, even though they are not part of the exercise sheets.

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := --this is doable
begin
split,
intro h,
split,
intro hp,
apply h,
left,
exact hp,
intro hq,
apply h,
right,
exact hq,
intro h,
cases h with hnp hnq,
intro h2,
cases h2,
apply hnp,
exact h2,
apply hnq,
exact h2,
end

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q :=
begin
split,
intro hnpq,
by_cases Q,
left,
intro hp,
apply hnpq,
split,
exact hp,
exact h,
right,
exact h,
intro h,
cases h with hnp hnq,
intro hpq,
cases hpq with hp hq,
apply hnp,
exact hp,
intro hpq,
cases hpq with hp hq,
apply hnq,
exact hq,
end