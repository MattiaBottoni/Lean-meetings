import tactic

/--We will use P, Q and R as our variables. In our case, the variables are statements (Prop)
which are either true or false.--/

variables (P Q R : Prop)


/--One of the most important tactic is "intro". You can use that if you have an implication
in your goal (what you want to prove) and would like to have the left side of the implication
as a hypothesis.
If you have a hypothesis that looks exactly as your goal, you can use the "exact" tactic to
prove the statement.
If your hypothesis is an implication and your goal looks like the righthand side of the
implication, use the "apply" tactic to change the goal to the lefthand side of the implication.
--/

example :  P → P :=
begin
intro h,
exact h, --here you could also use apply 
end

example: P → (P → Q) → Q:=
begin
intro hP,
intro hpq,
apply hpq, --here you have to use apply
exact hP,
end


/--You all saw the ∧ (and) and ∨ (or) symbols in the lecture. There are two different cases
to consider: once, when ∧ or ∨ are in the goal and once when they are in a hypothesis.
When they are in the goal, use the "split" tactic for ∧ and the "left" or "right" tactic for
∨. The "split" tactic will give you two goals where you have to prove the left side first and
then the right side. With the "left" or "right" tactic you decide which part you want to prove!
Do you understand why?
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

example : (P ∧ Q) → P :=
begin
intro hpq,
cases hpq with hp hq,
exact hp,
end

example : P → (P ∨ Q) :=
begin
intro hp,
left,
exact hp,
end 

example : Q → (P ∨ Q) :=
begin
intro hq,
right,
exact hq,
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

--keep in mind: ∧ is easy as an hypothesis, but not so easy to prove. 
--              ∨ is easy as to prove, but not so easy as an hypothesis.

--sheet 0 exercise 5.1.
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := --this is doable
begin
split, --split used here
intro hpqr, --intro used here
cases hpqr with hp hqr, --cases used here
cases hqr with hq hr,
left, --left used here
split,
exact hp, --exact used here
exact hq,
right, --right used here
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


