import Mathlib

def seq_converges_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε>0, ∃ N, ∀ n ≥ N, |a n - L| < ε

theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
  (a_leq_b : a ≤ b) (b_leq_c : b ≤ c)
  (a_to_L : seq_converges_to a L)
  (c_to_L : seq_converges_to c L) :
  seq_converges_to b L := by
