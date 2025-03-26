import Mathlib

-- Proof 1 of this theorem

theorem group_abelian (G : Type*) [Group G] (h : ∀ x : G, x * x = 1) : (∀ x y : G , x * y = y * x) := by 

intro x y 
have hxy := h (x*y)
have hyx := h (y*x)

have hxx := h x 
have hyy := h y
have mul : x * (x * y * (x * y)) = x * 1 := by rw[hxy]
repeat rw[← mul_assoc] at mul

rw[hxx] at mul
rw[one_mul] at mul
rw[mul_one] at mul


have new_mul : y * (y * x * y) = y * x := by rw[mul]
repeat rw[← mul_assoc] at new_mul

rw[hyy] at new_mul
rw[one_mul] at new_mul
exact new_mul
