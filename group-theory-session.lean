import Mathlib

/- Thm: in a group G, if all elements have order 2, then G is abelian -/

theorem order2_abelian (G : Type*) [Group G] (h : âˆ€ x : G, x*x = 1):
  (âˆ€ x y : G, x*y = y*x) := by

  intro x
  intro y

  have hx : x*x = 1 := by
    exact h x

  have hy : y*y = 1 := by
    exact h y

  have hhh : (y*x)*(y*x)=1 := by
    exact h (y*x)

  symm at hhh

  have hh : x*y*1 = x*y := by
    exact mul_one (x*y)

  rw [hhh] at hh

  repeat rw [â† mul_assoc] at hh

  nth_rewrite 4 [mul_assoc] at hh

  rw [hy] at hh

  rw [mul_one] at hh

  rw [hx] at hh

  rw [one_mul] at hh

  symm at hh

  exact hh

  /- *** :-) *** -/




/-  Thm: The center of a group is a subgroup   -/

def center2 {G : Type*} [Group G] : Subgroup G :=
{ carrier := { g | âˆ€ h : G, g * h = h * g },
  one_mem' := by
    intro g
    rw[one_mul, mul_one],  -- proof that 1 is in the center
  mul_mem' := by
    intro a b ha hb

    intro g
    specialize hb g
    specialize ha g
    rw [mul_assoc,hb,â† mul_assoc,ha,â† mul_assoc] ,  -- proof that the center is closed under multiplication
  inv_mem' := by

    simp
    intro x hx

    intro g
    specialize hx g

    have hx2 : x * g * xâ»Â¹ = g * x * xâ»Â¹ := by rw [hx]

    nth_rewrite 2 [mul_assoc] at hx2
    simp at hx2

    have hx3 : xâ»Â¹ * ( x * g * xâ»Â¹ ) = xâ»Â¹ * g := by rw [hx2]

    repeat rw [â† mul_assoc] at hx3
    simp at hx3
    /-
    symm
    exact hx3
    -/
    exact hx3.symm
     } -- proof that the center is closed under taking inverse

  /- *** :-) *** -/


def left_coset (G : Type*) [Group G] (H : Subgroup G) (g :  G) : Set G :=
  { g*h | h âˆˆ  H}

/- Theorem: cosets are either disjoint or equal   -/

theorem cosets_disjoint_or_equal (G : Type*) [Group G] (H : Subgroup G) :
  âˆ€ x y :  G, (left_coset G H x = left_coset G H y) âˆ¨
  ((left_coset G H x) âˆ© (left_coset G H y) = âˆ…) := by

  intro x y

  by_cases hyp_disjoint : (left_coset G H x) âˆ© (left_coset G H y) = âˆ…

  right

  exact hyp_disjoint

  left

  push_neg at hyp_disjoint
  have hyp : âˆƒ z, z âˆˆ ((left_coset G H x) âˆ© (left_coset G H y)) := by
    exact hyp_disjoint

  obtain âŸ¨g, hg âŸ© := hyp

  have h1: (g âˆˆ (left_coset G H x)) := by
    exact Set.mem_of_mem_inter_left hg

  unfold left_coset at h1

  rcases h1 with âŸ¨h_x, âŸ¨h_x_in_H, x_eqâŸ©âŸ©

  have h2: (g âˆˆ (left_coset G H y)) := by
    exact Set.mem_of_mem_inter_right hg

  unfold left_coset at h2
  simp at h2

  rcases h2 with âŸ¨h_y, âŸ¨h_y_in_H, y_eqâŸ©âŸ©

  symm at y_eq

  rw [y_eq] at x_eq

  have x_eq_2: x = y*h_y*h_xâ»Â¹ := by
    exact eq_mul_inv_of_mul_eq x_eq

  rw [mul_assoc] at x_eq_2

  have inv_h_x_in_H : h_xâ»Â¹ âˆˆ H := by
    exact (Subgroup.inv_mem_iff H).mpr h_x_in_H

  have prod_h_y_inv_h_x_in_H : h_y*h_xâ»Â¹ âˆˆ H := by
    exact H.mul_mem h_y_in_H inv_h_x_in_H

  apply Set.Subset.antisymm   /- proof by double inclusion -/

  intro g1
  intro g1_c

  unfold left_coset
  simp

  unfold left_coset at g1_c
  simp at g1_c

  obtain âŸ¨hg1,hyp_hg1 âŸ© := g1_c

  have hyp_hg1_2 : x*hg1 = g1 := by
    exact hyp_hg1.right

  have hyp_hg1_1 : hg1 âˆˆ H := by
    exact hyp_hg1.left

  rw [x_eq_2,mul_assoc] at hyp_hg1_2

  have hyp_prod3H : h_y*h_xâ»Â¹*hg1 âˆˆ H := by
    exact H.mul_mem prod_h_y_inv_h_x_in_H hyp_hg1_1

  use h_y*h_xâ»Â¹*hg1 /- goal xH âŠ† yH proved -/

  intro g2
  intro g2_c

  unfold left_coset
  simp

  unfold left_coset at g2_c
  simp at g2_c

  obtain âŸ¨hg2,hyp_hg2 âŸ© := g2_c

  have hyp_hg2_2 : y*hg2 = g2 := by
    exact hyp_hg2.right

  have hyp_hg2_1 : hg2 âˆˆ H := by
    exact hyp_hg2.left

  have y_eq_2 : y = x * (h_y*h_xâ»Â¹)â»Â¹ := by
    exact eq_mul_inv_of_mul_eq (id (Eq.symm x_eq_2))



  rw [y_eq_2,mul_assoc] at hyp_hg2_2

  rw [mul_inv_rev,inv_inv] at hyp_hg2_2

  have invH_y : h_yâ»Â¹ âˆˆ H := by exact (Subgroup.inv_mem_iff H).mpr h_y_in_H
  have hyp_inv_in_H : h_x*h_yâ»Â¹ âˆˆ H := by
    exact H.mul_mem h_x_in_H invH_y

  have hyp_prod3HH : (h_x*h_yâ»Â¹)*hg2 âˆˆ H := by
    exact H.mul_mem hyp_inv_in_H hyp_hg2_1

  use h_x*h_yâ»Â¹*hg2

/- *** :-) *** -/


-- Groups or order 2 are abelian 

/-- Any group of order 2 is commutative -/


theorem group_order_2_is_comm
    {G : Type*} [Group G] (h : Nat.card G = 2) : CommGroup G  := by

    constructor

    intro a b


    rw [Nat.card_eq_two_iff] at h

    obtain ⟨x, y, h_neq, h_all⟩ := h


    by_cases ha : a = 1
      rw [ha, one_mul, mul_one]

    by_cases hb : b = 1
      rw [hb, mul_one, one_mul]


    sorry
