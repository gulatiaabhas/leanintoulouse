import Mathlib

open Function

def irrep {K G V : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V]
  (ρ : Representation K G V) :
  Prop := (∀ (W : Submodule K V), (∀ g : G, ∀ v : V, v ∈ W → ρ g • v ∈ W) → (W = ⊥ ∨ W = ⊤))


def equivariant {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  (ρ : Representation K G V)
  (ρ' : Representation K G W)
  (f : V →ₗ[K] W) :
  Prop := ( ∀ g v, f (ρ g • v) = ρ' g • (f v))
-- • (\ smul) is used for group action (and for other things)

-- Schur's lemma : Let V and W be 2 irreps and f : V → W be equivariant. Then f=0 or f is an isomorphism

theorem schur_lemma1234 {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (ρ : Representation K G V) (ρ' : Representation K G W)
  (f : V →ₗ[K] W)
  (irr_rho : irrep ρ) (irr_rho' : irrep ρ')
  (equi_f : equivariant ρ ρ' f) :
  (f=0) ∨ (Bijective f) := by sorry
