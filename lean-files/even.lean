import Mathlib

def is_even (n : ℕ) : Prop := ∃ k : ℕ, n = 2*k

theorem even_mul {a b : ℕ} (ha : is_even a) : is_even (a*b) := by
  unfold is_even at *

  obtain ⟨k, hk⟩ := ha

  use k*b

  rw [hk]

  ring

theorem even_add {a  b : ℕ} (ha : is_even a) (hb : is_even b) : is_even (a+b) := by
  unfold is_even at *

  obtain ⟨k1, hk1⟩ := ha
  obtain ⟨k2, hk2⟩ := hb

  use k1+k2

  rw [hk1]
  rw [hk2]


  ring
