/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameEquation
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.GeneralizedCurveMarkingAffineRestriction

/-!
# The admissible frame change retains the original affine morphism

The explicit coordinate change agrees with both faithful evaluations in the
same original complement ring. Passing to spectra compares the actual
morphisms without assuming the complement is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingChartRingEquiv affineVariableChangeMap smoothMarkingWeierstrassCurve
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
  (e f : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "W" => smoothMarkingWeierstrassCurve E s e
local notation "V" => smoothMarkingWeierstrassCurve E s f
local notation "C" => smoothMarkingFrameChange E s e f
local notation "hC" => smoothMarkingFrameChange_equation E s e f
local notation "φ" => smoothMarkingComplementBaseMap E s
local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
  (Scheme.Hom.ker (Over.Hom.left (s ≫ E.inclusion)))) : E.curve.left.Opens)

/-- The explicit affine coordinate substitution commutes with both original evaluations. -/
theorem smoothMarkingChartRingEquiv_frameChange :
    (smoothMarkingChartRingEquiv E s e).toRingHom.comp
      (affineVariableChangeMap (V) (W) (C) (hC)).toRingHom =
        (smoothMarkingChartRingEquiv E s f).toRingHom := by
  let _ := (φ).toAlgebra
  let qe : Coordinate (W) 2 →ₐ[Γ(S, ⊤)] Γ((Scheme.Opens.toScheme (X := E.curve.left) (U)), ⊤) :=
    { (smoothMarkingChartRingEquiv E s e).toRingHom with
      commutes' := smoothMarkingChartRingEquiv_scalar E s e }
  let qf : Coordinate (V) 2 →ₐ[Γ(S, ⊤)] Γ((Scheme.Opens.toScheme (X := E.curve.left) (U)), ⊤) :=
    { (smoothMarkingChartRingEquiv E s f).toRingHom with
      commutes' := smoothMarkingChartRingEquiv_scalar E s f }
  suffices h : qe.comp (affineVariableChangeMap (V) (W) (C) (hC)) = qf by
    apply RingHom.ext
    intro z
    exact congrArg (fun a : Coordinate (V) 2 →ₐ[Γ(S, ⊤)] _ => a z) h
  apply WeierstrassIntegralChart.hom_ext
  intro i
  fin_cases i
  · change smoothMarkingChartRingEquiv E s e
      (affineVariableChangeMap (V) (W) (C) (hC) (coord (V) 2 0)) =
        smoothMarkingChartRingEquiv E s f (coord (V) 2 0)
    rw [affineVariableChangeMap_x]
    simp only [smoothMarkingFrameChange, map_mul, map_pow, map_zero,
      smoothMarkingChartRingEquiv_scalar, smoothMarkingChartRingEquiv_x, add_zero]
    simpa only [map_pow] using (smoothMarkingComplementX_frameChange E s e f).symm
  · change smoothMarkingChartRingEquiv E s e
      (affineVariableChangeMap (V) (W) (C) (hC) (coord (V) 2 1)) =
        smoothMarkingChartRingEquiv E s f (coord (V) 2 1)
    rw [affineVariableChangeMap_y]
    simp only [smoothMarkingFrameChange, map_mul, map_pow, map_zero,
      smoothMarkingChartRingEquiv_scalar,
      smoothMarkingChartRingEquiv_y, mul_zero, zero_mul, add_zero]
    simpa only [map_pow] using (smoothMarkingComplementY_frameChange E s e f).symm
  · change qe (affineVariableChangeMap (V) (W) (C) (hC) (coord (V) 2 2)) =
      qf (coord (V) 2 2)
    simp only [coord_self, map_one]

/-- The original affine coordinate morphism, in the integral cubic's chart algebra. -/
def smoothMarkingToIntegralAffineChart :
    (Scheme.Opens.toScheme (X := E.curve.left) (U)) ⟶ Spec (.of (Coordinate (W) 2)) :=
  (Scheme.Opens.toScheme (X := E.curve.left) (U)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (smoothMarkingChartRingEquiv E s e).toRingHom)

/-- This is the affine restriction of the original global cubic map. -/
theorem smoothMarkingToIntegralAffineChart_cubic :
    smoothMarkingToIntegralAffineChart E s e ≫ integralCurveChart (W) 2 =
      (Scheme.Opens.ι (X := E.curve.left) (U)) ≫ smoothMarkingToIntegralCubic E s e := by
  rw [smoothMarkingToIntegralCubic_affine, smoothMarkingToIntegralAffineChart,
    smoothMarkingToAffineCubic]
  simp only [Category.assoc, ← Spec.map_comp_assoc]
  unfold smoothMarkingChartRingEquiv
  rfl

/-- The actual affine morphisms commute with the constructed variable change. -/
theorem smoothMarkingToIntegralAffineChart_frameChange :
    smoothMarkingToIntegralAffineChart E s e ≫
      (affineVariableChangeIso (V) (W) (C) (hC)).hom =
        smoothMarkingToIntegralAffineChart E s f := by
  change smoothMarkingToIntegralAffineChart E s e ≫
    Spec.map (CommRingCat.ofHom (affineVariableChangeMap (V) (W) (C) (hC)).toRingHom) = _
  simp only [smoothMarkingToIntegralAffineChart, Category.assoc, ← Spec.map_comp]
  change _ ≫ Spec.map (CommRingCat.ofHom ((smoothMarkingChartRingEquiv E s e).toRingHom.comp
    (affineVariableChangeMap (V) (W) (C) (hC)).toRingHom)) = _
  rw [smoothMarkingChartRingEquiv_frameChange]

end FLT.Mazur.GeneralizedEllipticCurve
