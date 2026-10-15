/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Exact geometric image of a tensor principal open

Keep the localization range calculation independent of large chart algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A : Type u} [CommRing A] [Algebra R A] (x : A)

/-- The tensor principal inclusion has exactly the original tensor-coordinate basic open. -/
theorem inclusion_range : Set.range (inclusion S x) =
    (PrimeSpectrum.basicOpen ((1 : S) ⊗ₜ[R] x) : Set (PrimeSpectrum (S ⊗[R] A))) :=
  PrimeSpectrum.localization_away_comap_range _ _

/-- Membership in the full tensor principal chart is nonvanishing of its original function. -/
theorem mem_inclusion_range (z : Spec (.of (S ⊗[R] A))) :
    z ∈ Set.range (inclusion S x) ↔ (1 : S) ⊗ₜ[R] x ∉ z.asIdeal := by
  rw [inclusion_range]
  rfl

end FLT.Mazur.PrincipalOpenTensor
