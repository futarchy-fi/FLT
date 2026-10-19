/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualFibers

/-!
# The continuous comparison to the full residual invariant spectrum

The original scheme map to the full residual spectrum factors continuously
through the actual quotient open. Full residual functions therefore define
quotient opens whose affine-source preimages are the exact ordinary basic opens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The actual quotient-open map to the spectrum of full residual affine invariants. -/
def orbitToResidualSpectrum (z : affineOrbitOpen n i) : affineResidualSpectrum n i :=
  affineResidualProjection n i ((affineOrbitProjection_surjective n i z).choose)

/-- The factorization agrees exactly with the original affine scheme projection. -/
theorem orbitToResidualSpectrum_projection (x : invariantAffineChart n i) :
    orbitToResidualSpectrum n i (affineOrbitProjection n i x) =
      affineResidualProjection n i x :=
  affineResidualProjection_eq_of_orbit_eq n i
    (affineOrbitProjection_surjective n i (affineOrbitProjection n i x)).choose_spec

/-- The actual quotient topology makes the full residual spectrum comparison continuous. -/
theorem orbitToResidualSpectrum_continuous : Continuous (orbitToResidualSpectrum n i) := by
  apply (affineOrbitProjection_isQuotientMap n i).continuous_iff.mpr
  have h : orbitToResidualSpectrum n i ∘ affineOrbitProjection n i =
      affineResidualProjection n i := funext (orbitToResidualSpectrum_projection n i)
  rw [h]
  exact (affineResidualProjection n i).continuous

/-- Every full residual affine invariant gives a genuine quotient-open principal domain. -/
def affineResidualPrincipal (s : affineResidualSections n i) : Opens (affineOrbitOpen n i) :=
  ⟨orbitToResidualSpectrum n i ⁻¹' (PrimeSpectrum.basicOpen s).carrier,
    (PrimeSpectrum.basicOpen s).isOpen.preimage (orbitToResidualSpectrum_continuous n i)⟩

/-- Pullback of that domain is exactly the original affine basic open of the invariant. -/
theorem affineResidualPrincipal_preimage (s : affineResidualSections n i) :
    affineOrbitProjection n i ⁻¹' (affineResidualPrincipal n i s).carrier =
      ((invariantAffineChart n i).basicOpen s.val).carrier := by
  have h := congrArg SetLike.coe (SchemeRelationInvariantSpectrum.projection_preimage_basicOpen
    (affineResidualSource n i) (affineResidualTarget n i) s)
  ext x
  change orbitToResidualSpectrum n i (affineOrbitProjection n i x) ∈
    (PrimeSpectrum.basicOpen s).carrier ↔ x ∈ (invariantAffineChart n i).basicOpen s.val
  rw [orbitToResidualSpectrum_projection]
  exact Set.ext_iff.mp h x

end FLT.Mazur.CyclicCharacteristicOrbit
