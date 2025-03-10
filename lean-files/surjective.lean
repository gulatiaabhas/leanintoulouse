import Mathlib

variable (X Y Z : Type)
variable (f : X -> Y)
variable (g : Y -> Z)

open Function

example (hf : Surjective f) (hg : Surjective g) :
  Surjective (g ∘ f) := by

  unfold Surjective at *

  intro z

  specialize hg z
  change ∃ y, g y = z at hg
  rcases hg with ⟨y, hy⟩

  specialize hf y
  change ∃ x, f x = y at hf
  rcases hf with ⟨x, hx⟩

  use x

  rw [<- hy]
  rw [<- hx]

  rfl
