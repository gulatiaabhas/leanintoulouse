import Mathlib

def seq_converges_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε>0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε

theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
  (a_leq_b : a ≤ b) (b_leq_c : b ≤ c)
  (a_to_L : seq_converges_to a L)
  (c_to_L : seq_converges_to c L) :
  seq_converges_to b L := by
  unfold seq_converges_to
  unfold seq_converges_to at a_to_L
  unfold seq_converges_to at c_to_L


  intro ε ε_pos

  obtain ⟨N₁, hN₁⟩ := a_to_L ε ε_pos
  obtain ⟨N₂, hN₂⟩ := c_to_L ε ε_pos

  let N : ℕ := max N₁ N₂
  have N₁_leq_N : N₁ ≤ N := by
    exact le_max_left N₁ N₂
  have N₂_leq_N : N₂ ≤ N := by
    exact le_max_right N₁ N₂

  exists N
  intro n N_leq_n

  rw [abs_le]
  constructor

  -- prove ε <= b n - L
  have N₁_leq_n : N₁ ≤ n := by
    apply le_trans N₁_leq_N N_leq_n

  specialize hN₁ n N₁_leq_n
  rw [abs_le] at hN₁
  obtain ⟨ineq_a_1, ineq_a_2⟩ := hN₁

  have a_leq_b_at_n : a n ≤ b n:= a_leq_b n
  have aL_leq_bL_at_n : a n - L ≤ b n - L := sub_le_sub_right a_leq_b_at_n L
  exact le_trans ineq_a_1 aL_leq_bL_at_n


  -- prove b n - L <= ε
  have N₂_leq_n : N₂ ≤ n := by
    apply le_trans N₂_leq_N N_leq_n

  specialize hN₂ n N₂_leq_n
  rw [abs_le] at hN₂
  obtain ⟨ineq_c_1, ineq_c_2⟩ := hN₂

  have b_leq_c_at_n : b n ≤ c n:= b_leq_c n
  have bL_leq_cL_at_n : b n - L ≤ c n - L := sub_le_sub_right b_leq_c_at_n L
  exact le_trans bL_leq_cL_at_n ineq_c_2
