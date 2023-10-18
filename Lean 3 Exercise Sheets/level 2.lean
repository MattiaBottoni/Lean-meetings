import tactic
import data.real.basic

--In order to manipulate equations in Lean (which you will need to do in exercise 2.1),
--you need to know a lot of tactics. I will show you here how to they are used, but I also
--wrote a cheat sheet were they are all on. So if you prefer to directly solve exercise 2.1,
--you can skip the next part.

variables (a b c : ℝ)


example :  (a - b = 0) ↔ (a = b) :=
begin
split,
intro h,
rw sub_eq_zero at h,
--or rw ← sub_eq_zero,
exact h,
intro h,
rw sub_eq_zero,
--or rw ← sub_eq_zero at h,
exact h,
end

example : (a - b - c = 5) ↔ (a - (b + c) = 5) :=
begin
split,
intro h,
rw sub_sub at h,
-- or rw ← sub_sub,
exact h,
intro h,
rw sub_sub,
--or rw ← sub_sub at h,
exact h,
end

example : (a + b = 5) ↔ (b + a = 5) :=
begin
split,
intro h,
rw add_comm, --here we use add_comm in the goal.
exact h,
intro h,
rw add_comm at h, --here we use add_comm in the hypothesis
exact h,
end

example : (a + b - c = 5) ↔ (a + (b - c) = 5) :=
begin
split,
intro h,
rw add_sub,
--or rw ← add_sub at h,
exact h,
intro h,
rw ← add_sub,
--or rw add_sub at h,
exact h,
end

example : (a^2 - b^2 = 5) ↔ ((a+b)*(a-b) = 5) :=
begin
split,
intro h,
rw ← sq_sub_sq,
--or rw sq_sub_sq at h,
exact h,
intro h,
rw sq_sub_sq,
--or rw ← sq_sub_sq at h,
exact h,
end

example : (a - b = 5) ↔ (a + -b = 5) :=
begin
split,
intro h,
rw sub_eq_add_neg at h,
--or rw ← sub_eq_add_neg,
exact h,
intro h,
rw ← sub_eq_add_neg at h,
--or rw sub_eq_add_neg,
exact h, 
end

example : (a + b + c = 5) ↔ (a + (b + c) = 5) :=
begin
split,
intro h,
rw add_assoc at h,
--from now on, I won't right the other possibility anymore.
exact h,
intro h,
rw ← add_assoc at h,
exact h,
end

example : (a + b + c = 5) ↔ (a + c + b = 5) :=
begin
split,
intro h,
rw add_assoc at h,
rw add_comm b c at h,
rw ← add_assoc at h,
exact h,
intro h,
rw add_assoc at h,
rw add_comm c b at h,
rw ← add_assoc at h,
exact h, 
end

example : (a - b + c = 5) ↔ (a - (b - c) = 5) :=
begin
split,
intro h,
rw sub_add at h,
exact h,
intro h,
rw ← sub_add at h,
exact h, 
end

example : (a * (b - c) = 5) ↔ (a * b - a * c = 5) :=
begin
split,
intro h,
rw mul_sub at h,
exact h,
intro h,
rw ← mul_sub at h,
exact h,
end

example : ((a - b) * c = 5) ↔ (a * c - b * c = 5) :=
begin
split,
intro h,
rw sub_mul at h,
exact h,
intro h,
rw ← sub_mul at h,
exact h,
end

example : (a * b = 0) ↔ (a = 0 ∨ b = 0) :=
begin
split,
intro h,
rw mul_eq_zero at h,
cases h,
left,
exact h,
right,
exact h,
intro h,
rw mul_eq_zero,
cases h,
left,
exact h,
right,
exact h,
end

---------------------------------------------------------------------------------------
--exercise 2.1.
example (x y : ℝ) :  (x ^ 2 + 5 * y = y ^ 2 + 5 * x) → ((x = y) ∨ (x + y = 5)) :=
begin
intro h,
rw ← sub_eq_zero at h,
rw ← sub_sub at h,
rw add_comm  at h, 
rw ← add_sub at h,
rw add_comm at h,
rw sq_sub_sq at h,
rw sub_eq_add_neg at h,
rw add_assoc at h,
rw add_comm (5*y) (-(5*x)) at h,
rw ← add_assoc at h,
rw ← sub_eq_add_neg at h,
rw sub_add at h, 
rw ← mul_sub at h,
rw ← sub_mul at h,
rw mul_eq_zero at h,
cases h,
right,
rw sub_eq_zero at h,
exact h,
left,
rw sub_eq_zero at h,
exact h,
end


--exercise 2.2.
--For this exercise you will need the "by_cases" tactic (which you learned in exercise sheet 1)
--and the "left", "right" tactics.

example (a : ℤ) : (a ^ 2 ∣ a) → ((a = -1) ∨ (a = 1) ∨ (a = 0)) :=
begin
intro h,
by_cases h2 : a = 0,
right,
right,
exact h2,
by_cases h3 : a = 1,
right,
left,
exact h3,
by_cases h4 : a = -1,
left,
exact h4,
exfalso,
rw sq at h,
--rw dvd_iff_dvd_of_dvd_mul at h,
sorry,
end

--exercise 2.3.
--We will do this one on paper.


--exercise 3.1.
example (x : ℝ) : (x ≤ -1) → (x ^ 3 - x) ≤ 0 :=
begin
intro h,
have h2 : (x+1) ≤ 0,
linarith,
rw pow_three,
rw ← mul_one x,
rw mul_assoc,
rw ← mul_sub,
rw mul_one x,
rw one_mul,
rw ← pow_two,
--have h3 : x * (x^2-1) ≤ 0,
rw mul_nonpos_iff,
right,
split,
linarith,
nlinarith,
--nlinarith, --reuse if you use h3,
end


--exercise 3.2.
example (x y z : ℤ) : ((x ∣ y) ∨ (x ∣ z)) → (x ∣ y * z) :=
begin
intro h,
cases h with hy hz,
exact dvd_mul_of_dvd_left hy z,
exact dvd_mul_of_dvd_right hz y,
end

--exercise 4.1.
example (a b c : ℤ) (h : a^2 + b^2 = c^2) : (a % 2 = 1) ∨ (b % 2 = 1) :=
begin
sorry,
end


--exercise 4.2.


--execise 5.1.
variables
  (X : Type)
  (A B C : set X)
  (x y z : X)   


open set

example (hc : y ∈ C): (A ×ˢ C) = (B ×ˢ C) → A = B :=
begin
intro h,
ext,
split,
intro ha,
have hx : (x,y) ∈ (A ×ˢ C),
split,
exact ha,
exact hc,
rw h at hx,
exact hx.1,
intro hb,
have hx : (x,y) ∈ (B ×ˢ C),
split,
exact hb,
exact hc,
rw eq_comm at h,
rw h at hx,
exact hx.1,
end


--exercise 5.2.
example : 𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B) :=
begin
  ext,
  split,
  intro h,
  rw mem_powerset_iff at h,
  rw subset_inter_iff at h,
  cases h with ha hb,
  split,
  rw mem_powerset_iff,
  exact ha,
  exact hb,
  intro h,
  rw mem_inter_iff at h,
  cases h with ha hb,
  rw mem_powerset_iff at ha,
  rw mem_powerset_iff at hb,
  rw mem_powerset_iff,
  rw subset_inter_iff,
  split,
  exact ha,
  exact hb,
end