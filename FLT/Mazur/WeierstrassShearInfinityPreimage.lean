/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearData
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassCoefficientChartPreimage
public import FLT.Mazur.WeierstrassIntegralCurveTwoChartCover

/-!
# The actual infinity preimage under integral shear

The affine chart is preserved, while the original Y-chart pulls back to a
different open. On the affine chart its defining function is y+r*x.
These actual inverse-image opens cover the sheared integral cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (r : R)
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "i" => integralVariableChangeIso W U C rfl

/-- The original affine chart square is cartesian under integral shear. -/
theorem integralShear_affine_isPullback :
    IsPullback (affineVariableChangeIso W U C rfl).hom (integralCurveChart U 2)
      (integralCurveChart W 2) (i).hom :=
  IsPullback.of_horiz_isIso ⟨(integralVariableChangeIso_affine W U C rfl).symm⟩

/-- The full inverse image of the original affine chart is exactly the sheared affine chart. -/
theorem integralShear_affine_preimage :
    (i).hom ⁻¹ᵁ (integralCurveChart W 2).opensRange = (integralCurveChart U 2).opensRange := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (integralShear_affine_isPullback W r) ⊤
  simpa using h.symm

/-- The original infinity boundary pulls back to D(y+r*x) on the sheared affine chart. -/
theorem integralShear_infinity_affine_preimage :
    (integralCurveChart U 2 ≫ (i).hom) ⁻¹ᵁ (integralCurveChart W 1).opensRange =
      PrimeSpectrum.basicOpen (coord U 2 1 + algebraMap R (Coordinate U 2) r * coord U 2 0) := by
  rw [integralVariableChangeIso_affine, Scheme.Hom.comp_preimage,
    integralCurveChart_preimage_chart]
  change Spec.map (CommRingCat.ofHom (affineVariableChangeMap W U C rfl).toRingHom) ⁻¹ᵁ
    PrimeSpectrum.basicOpen (coord W 2 1) = _
  rw [SpecMap_preimage_basicOpen]
  congr 1
  change affineVariableChangeMap W U C rfl (coord W 2 1) = _
  simp only [affineVariableChangeMap_y, Units.val_one, map_one, one_pow, one_mul,
    map_zero, add_zero]

/-- The actual translated infinity open and the preserved affine open cover the entire cubic. -/
theorem integralShear_infinity_affine_cover :
    ((i).hom ⁻¹ᵁ (integralCurveChart W 1).opensRange) ⊔
      (integralCurveChart U 2).opensRange = ⊤ := by
  rw [← integralShear_affine_preimage W r]
  ext z
  change ((i).hom z ∈ Set.range (integralCurveChart W 1) ∨
    (i).hom z ∈ Set.range (integralCurveChart W 2)) ↔ True
  exact iff_true_intro (integralCurve_yz_cover W ((i).hom z))

end FLT.Mazur.WeierstrassIntegralChart
