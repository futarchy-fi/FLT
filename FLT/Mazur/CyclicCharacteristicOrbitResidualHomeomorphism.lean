/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicResidualSpectrumHomeomorphism
public import FLT.Mazur.CyclicCharacteristicAffineResidualTopology
public import FLT.Mazur.CyclicCharacteristicOrbitComparisons

/-!
# The original affine orbit open is homeomorphic to its full residual spectrum

The homeomorphism is the previously constructed map, with its exact original
projection factorization. This identifies topology, without asserting sheaf affineness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Equality in the actual finite quotient implies equality in the full affine orbit open. -/
theorem affineOrbitProjection_eq_of_finite_eq (x y : invariantAffineChart n i)
    (h : invariantAffineQuotientMap n i x = invariantAffineQuotientMap n i y) :
    affineOrbitProjection n i x = affineOrbitProjection n i y := by
  apply Subtype.ext
  apply projection_eq_of_finite_quotient_eq n i.1
  have he := congrArg (invariantAffineQuotientInclusion n i) h
  change (invariantAffineQuotientMap n i ≫ invariantAffineQuotientInclusion n i) x =
    (invariantAffineQuotientMap n i ≫ invariantAffineQuotientInclusion n i) y at he
  rwa [invariantAffineQuotientMap_inclusion] at he

/-- The full residual spectrum projection gives exactly its scheme quotient topology. -/
theorem affineResidualProjection_isQuotientMap :
    IsQuotientMap (affineResidualProjection n i) := by
  have h := (affineFiniteToResidualSpectrum_isHomeomorph n i).isQuotientMap.comp
    (SchemeFiniteGroupQuotient.quotientMap_isQuotientMap (invariantAffineAction n i))
  change IsQuotientMap
    (fun x => (invariantAffineQuotientMap n i ≫ affineFiniteToResidualSpectrum n i) x) at h
  rwa [affineFiniteToResidualSpectrum_projection] at h

/-- The retained original orbit-to-spectrum comparison detects the quotient topology. -/
theorem orbitToResidualSpectrum_isQuotientMap :
    IsQuotientMap (orbitToResidualSpectrum n i) := by
  apply (affineOrbitProjection_isQuotientMap n i).of_comp_isQuotientMap
  have he : orbitToResidualSpectrum n i ∘ affineOrbitProjection n i =
      affineResidualProjection n i := funext (orbitToResidualSpectrum_projection n i)
  rw [he]
  exact affineResidualProjection_isQuotientMap n i

/-- Original full residual functions separate the points of the actual affine orbit open. -/
theorem orbitToResidualSpectrum_injective :
    Function.Injective (orbitToResidualSpectrum n i) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := affineOrbitProjection_surjective n i a
  obtain ⟨y, rfl⟩ := affineOrbitProjection_surjective n i b
  rw [orbitToResidualSpectrum_projection, orbitToResidualSpectrum_projection] at hab
  apply affineOrbitProjection_eq_of_finite_eq n i x y
  apply (affineFiniteToResidualSpectrum_isHomeomorph n i).injective
  change (invariantAffineQuotientMap n i ≫ affineFiniteToResidualSpectrum n i) x =
    (invariantAffineQuotientMap n i ≫ affineFiniteToResidualSpectrum n i) y
  rwa [affineFiniteToResidualSpectrum_projection]

/-- The comparison already underlying the locally ringed map is a homeomorphism. -/
theorem orbitToResidualSpectrum_isHomeomorph :
    IsHomeomorph (orbitToResidualSpectrum n i) :=
  isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨orbitToResidualSpectrum_isQuotientMap n i, orbitToResidualSpectrum_injective n i⟩

/-- The homeomorphism retains the exact original orbit-to-spectrum function. -/
def orbitResidualHomeomorph : affineOrbitOpen n i ≃ₜ affineResidualSpectrum n i :=
  (orbitToResidualSpectrum_isHomeomorph n i).homeomorph (orbitToResidualSpectrum n i)

/-- Its underlying function is the original comparison. -/
theorem orbitResidualHomeomorph_apply (z : affineOrbitOpen n i) :
    orbitResidualHomeomorph n i z = orbitToResidualSpectrum n i z := rfl

end FLT.Mazur.CyclicCharacteristicOrbit
