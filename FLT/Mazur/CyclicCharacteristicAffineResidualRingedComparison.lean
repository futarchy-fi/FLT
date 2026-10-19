/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualComparison
public import FLT.Mazur.CyclicCharacteristicAffineResidualTopology
public import FLT.Mazur.CyclicCharacteristicAffineSectionEquivalence

/-!
# The actual locally ringed comparison to the full residual spectrum

The reconstructed section-ring equivalence identifies the two affine spectrum
targets. Transport gives a locally ringed comparison from the actual quotient
open, whose base map is the continuous comparison already constructed.
This does not yet assert that the quotient open is an affine scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The comparison of the two affine targets is induced by an actual ring equivalence. -/
instance affineResidualComparison_isIso : IsIso (affineResidualComparison n i) := by
  change IsIso (Spec.map (affineResidualSectionsEquiv n i).toCommRingCatIso.hom)
  infer_instance

/-- The two spectra are isomorphic through the original section pullback. -/
def affineResidualComparisonIso :
    affineResidualSpectrum n i ≅ invariantAffineTarget n (affineOrbitOpen n i) :=
  asIso (affineResidualComparison n i)

/-- The actual locally ringed quotient-open comparison to its full residual spectrum. -/
def affineResidualRingedComparison : invariantOpenSpace n (affineOrbitOpen n i) ⟶
    (affineResidualSpectrum n i).toLocallyRingedSpace :=
  invariantAffineComparison n (affineOrbitOpen n i) ≫
    (affineResidualComparisonIso n i).inv.toLRSHom

/-- The original affine source recovers the full residual spectrum projection. -/
@[reassoc] theorem affineToInvariantOpen_residualComparison :
    affineToInvariantOpen n i ≫ affineResidualRingedComparison n i =
      (affineResidualProjection n i).toLRSHom := by
  unfold affineResidualRingedComparison
  rw [← Category.assoc]
  change (affineChartComparison n i).toLRSHom ≫ _ = _
  rw [← affineResidualProjection_comparison, Scheme.Hom.comp_toLRSHom, Category.assoc]
  change (affineResidualProjection n i).toLRSHom ≫
    ((affineResidualComparisonIso n i).hom ≫
      (affineResidualComparisonIso n i).inv).toLRSHom = _
  rw [Iso.hom_inv_id]
  exact Category.comp_id _

/-- The new locally ringed comparison has exactly the previously constructed continuous map. -/
theorem affineResidualRingedComparison_base (z : affineOrbitOpen n i) :
    (affineResidualRingedComparison n i).base z = orbitToResidualSpectrum n i z := by
  obtain ⟨x, rfl⟩ := affineOrbitProjection_surjective n i z
  rw [orbitToResidualSpectrum_projection]
  have h := congrArg (fun f => f.base x) (affineToInvariantOpen_residualComparison n i)
  change (affineResidualRingedComparison n i).base ((affineToInvariantOpen n i).base x) =
    affineResidualProjection n i x at h
  rw [affineToInvariantOpen_base] at h
  exact h

end FLT.Mazur.CyclicCharacteristicOrbit
