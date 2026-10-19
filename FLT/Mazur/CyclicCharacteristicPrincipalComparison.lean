/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicComparisonNaturality
public import FLT.Mazur.CyclicCharacteristicInvariantPrincipalSpectrum
public import FLT.Mazur.LocallyRingedOpenBasic

/-!
# Compatibility of principal orbit restrictions and affine comparisons

The original locally ringed comparison sends an actual invariant principal
restriction into the corresponding spectrum basic open. The resulting square
commutes as locally ringed morphisms, and its underlying inverse image is exact.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))
  (s : (invariantSheaf n).obj.obj (op W))
local notation "D" => invariantPrincipal n W s
local notation "h" => invariantPrincipal_le n W s

/-- Principal restriction is the actual orbit-open restriction on affine targets. -/
theorem invariantAffineRestriction_principal :
    invariantAffineRestriction n h = invariantAffinePrincipalMap n W s := rfl

/-- The principal comparison square commutes with the original restriction morphisms. -/
@[reassoc] theorem invariantAffineComparison_principal :
    invariantOpenInclusion n h ≫ invariantAffineComparison n W =
      invariantAffineComparison n D ≫ (invariantAffinePrincipalMap n W s).toLRSHom :=
  invariantAffineComparison_naturality n h

/-- The target basic open pulls back to precisely the actual principal orbit domain. -/
theorem invariantAffineComparison_preimage_principal :
    (invariantAffineComparison n W).base ⁻¹'
      (invariantAffineBasicOpen n W s : Set _) = {x : W | x.val ∈ D} := by
  change (invariantAffineComparison n W).base ⁻¹'
    (PrimeSpectrum.basicOpen s).carrier = _
  rw [invariantAffineComparison_preimage_basicOpen]
  exact congrArg SetLike.coe
    (LocallyRingedOpenInclusion.sectionsIso_basicOpen (invariantLocallyRingedSpace n) W s)

/-- The principal inclusion has exactly the inverse image of the affine principal map. -/
theorem invariantOpenInclusion_principal_range :
    Set.range (invariantOpenInclusion n h).base =
      (invariantAffineComparison n W).base ⁻¹'
        Set.range (invariantAffinePrincipalMap n W s).toLRSHom.base := by
  change Set.range (invariantOpenInclusion n h).base =
    (invariantAffineComparison n W).base ⁻¹' Set.range (invariantAffinePrincipalMap n W s)
  rw [invariantAffinePrincipalMap_range, invariantAffineComparison_preimage_principal]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [invariantOpenInclusion_base]
    exact y.property
  · intro hx
    refine ⟨⟨x.val, hx⟩, ?_⟩
    exact (invariantOpenInclusion_base n h _).trans (Subtype.ext rfl)

/-- Factoring through the actual affine open subscheme preserves the comparison square. -/
@[reassoc] theorem invariantAffineComparison_principalIso :
    (invariantAffineComparison n D ≫ (invariantAffinePrincipalIso n W s).hom.toLRSHom) ≫
      (invariantAffineBasicOpen n W s).ι.toLRSHom =
        invariantOpenInclusion n h ≫ invariantAffineComparison n W := by
  rw [Category.assoc, ← Scheme.Hom.comp_toLRSHom, invariantAffinePrincipalIso_inclusion,
    invariantAffineComparison_principal]

end FLT.Mazur.CyclicCharacteristicOrbit
