import Mathlib

variable {K V : Type*} [Field K]
variable [AddCommGroup V] [Module K V]
variable (f : V →ₗ[K] V) -- to write  ₗ : \ _ l (without the spaces)

open Function

-- ⊥ : \ bot. The set of all submodules forms a partially ordered structure, ⊥ means the smallest element
-- we can used Submodule.span K {0}
-- \ iff to write ↔

theorem injective_iff_kernel_eq_zero : (Injective f) ↔ (LinearMap.ker f = ⊥) := by

  -- exact Iff.symm LinearMap.ker_eq_bot
  constructor
  -- Goal : f injective => ker(f)=0
  intro h_inj
  unfold Injective at h_inj -- not needed

  ext v -- struggled here! apply Set.Subset.antisymm is not working?

  -- Now the goal is : v in Ker(f) <=> v = 0
  constructor
  -- Goal : v in Ker(f) => v = 0
  intro h_v

  have h_eq_zero : f v = f 0 := by  rw [h_v, LinearMap.map_zero f]
  simp
  apply h_inj h_eq_zero -- goal proved

  /-
  have h_zero : f 0 = 0 := by exact LinearMap.map_zero f
  have h_eq_zero : f v = f 0 := by rw [h_v, h_zero]
  apply h_inj h_eq_zero -- goal proved
  -/

  -- Goal : v=0 => v in Ker(f)
  intro Hv0

  have hv1 : f v = 0 := by rw [Hv0, LinearMap.map_zero f]
  exact hv1

  /-
  have Hv1 : v = 0 := by exact Hv0
  have hv0 : f v = f 0 := by rw [Hv1]
  have h_zero : f 0 = 0 := by exact LinearMap.map_zero f
  have hv1 : f v = 0 := by rw [hv0,h_zero]
  exact hv1
  -/

  -- the other way : Ker(f)=0 => f injective

  intro H
  unfold Injective -- not needed
  intro a b
  intro Hab

  have Hab_0 : f (a-b) = 0 := by rw[LinearMap.map_sub f a b, sub_eq_zero_of_eq Hab]

  have hab_Ker : a-b ∈ LinearMap.ker f := by exact Hab_0

  rw [H] at hab_Ker

  have a_eq_b : a - b = 0 := by exact hab_Ker

  exact eq_of_sub_eq_zero a_eq_b
