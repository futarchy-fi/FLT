/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualSections

/-!
# Comparing the refined full residual spectrum with the invariant sheaf spectrum

The actual sheaf pullback gives a scheme morphism between the two affine targets.
Its composite with the original affine source projection is precisely the original
locally ringed comparison. This records the remaining ring comparison explicitly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The original affine parameter map into the spectrum of actual quotient sheaf sections. -/
def affineChartComparison : invariantAffineChart n i ⟶
    invariantAffineTarget n (affineOrbitOpen n i) :=
  ⟨affineToInvariantOpen n i ≫ invariantAffineComparison n (affineOrbitOpen n i)⟩

/-- The comparison preserves the entire restricted residual relation as scheme morphisms. -/
@[reassoc] theorem affineChartComparison_condition :
    affineResidualSource n i ≫ affineChartComparison n i =
      affineResidualTarget n i ≫ affineChartComparison n i := by
  apply Scheme.Hom.ext'
  change (affineResidualSource n i).toLRSHom ≫ affineToInvariantOpen n i ≫ _ =
    (affineResidualTarget n i).toLRSHom ≫ affineToInvariantOpen n i ≫ _
  rw [← Category.assoc, ← Category.assoc, affineToInvariantOpen_condition]

/-- The comparison between the full residual spectrum and the actual sheaf-section spectrum. -/
def affineResidualComparison : affineResidualSpectrum n i ⟶
    invariantAffineTarget n (affineOrbitOpen n i) :=
  Spec.map (CommRingCat.ofHom (affineResidualSectionMap n i))

/-- Its pullback along the original affine parameter map is the exact locally ringed comparison. -/
@[reassoc] theorem affineResidualProjection_comparison :
    affineResidualProjection n i ≫ affineResidualComparison n i =
      affineChartComparison n i := by
  apply Scheme.Hom.ext'
  have h := identityToΓSpec.naturality (affineToInvariantOpen n i)
  change affineToInvariantOpen n i ≫
      (invariantOpenSpace n (affineOrbitOpen n i)).toΓSpec =
    (invariantAffineChart n i).toLocallyRingedSpace.toΓSpec ≫
      Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map (affineToInvariantOpen n i).op)
    at h
  change ((invariantAffineChart n i).toSpecΓ ≫
      Spec.map (SchemeRelationInvariantSpectrum.inclusion
        (affineResidualSource n i) (affineResidualTarget n i)) ≫
      Spec.map (CommRingCat.ofHom (affineResidualSectionMap n i))).toLRSHom =
    affineToInvariantOpen n i ≫ invariantAffineComparison n (affineOrbitOpen n i)
  rw [← Spec.map_comp]
  change _ = affineToInvariantOpen n i ≫
    (invariantOpenSpace n (affineOrbitOpen n i)).toΓSpec ≫ _
  rw [← Category.assoc, h, Category.assoc, ← Spec.locallyRingedSpaceMap_comp]
  rfl

/-- The retained affine source detects this comparison uniquely among maps to the affine target. -/
theorem affineResidualComparison_unique
    (g : affineResidualSpectrum n i ⟶ invariantAffineTarget n (affineOrbitOpen n i))
    (hg : affineResidualProjection n i ≫ g = affineChartComparison n i) :
    g = affineResidualComparison n i := by
  let _ : IsAffine (invariantAffineTarget n (affineOrbitOpen n i)) := by
    unfold invariantAffineTarget
    infer_instance
  exact SchemeRelationInvariantSpectrum.affine_hom_ext _ _
    (hg.trans (affineResidualProjection_comparison n i).symm)

end FLT.Mazur.CyclicCharacteristicOrbit
