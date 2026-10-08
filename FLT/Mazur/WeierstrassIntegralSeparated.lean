/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChartIntersection
public import FLT.Mazur.WeierstrassOverlapDiagonalAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Separatedness of the integral Weierstrass cubic

The actual diagonal restricts on each pair of affine charts to the spectrum
of the surjective overlap algebra. Descent of closed immersions proves that
the glued cubic is separated over its coefficient spectrum.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)

/-- The product of any two atlas charts is the spectrum of their tensor product. -/
def integralChartPairIso :
    pullback (integralCurveChart W j ≫ integralCurveStructure W)
      (integralCurveChart W k ≫ integralCurveStructure W) ≅
        Spec (.of (ChartProduct W j k)) :=
  pullback.congrHom (integralCurveChart_structure W j) (integralCurveChart_structure W k) ≪≫
    pullbackSpecIso R (Coordinate W j) (Coordinate W k)

/-- The tensor comparison preserves the first chart input. -/
@[reassoc] theorem integralChartPairIso_inv_fst :
    (integralChartPairIso W j k).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (chartProductLeft W j k).toRingHom) := by
  simp [integralChartPairIso, chartStructure, chartProductLeft, Algebra.TensorProduct.includeLeft]

/-- The tensor comparison preserves the second chart input. -/
@[reassoc] theorem integralChartPairIso_inv_snd :
    (integralChartPairIso W j k).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (chartProductRight W j k).toRingHom) := by
  simp [integralChartPairIso, chartStructure, chartProductRight]

/-- The overlap algebra is exactly the restriction of the scheme diagonal. -/
theorem integralChartDiagonal_comparison :
    (integralChartIntersectionIso W j k).hom ≫
        pullback.mapDesc (integralCurveChart W j) (integralCurveChart W k)
          (integralCurveStructure W) =
      Spec.map (CommRingCat.ofHom (overlapDiagonalAlgebra W j k).toRingHom) ≫
        (integralChartPairIso W j k).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.mapDesc, pullback.map, pullback.lift_fst,
      Category.comp_id, integralChartIntersectionIso_fst, integralChartPairIso_inv_fst]
    rw [← Spec.map_comp]
    change Spec.map _ = Spec.map _
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun a => (overlapDiagonalAlgebra_left W j k a).symm)
  · simp only [Category.assoc, pullback.mapDesc, pullback.map, pullback.lift_snd,
      Category.comp_id, integralChartIntersectionIso_snd, integralChartPairIso_inv_snd]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change transition W j k (algebraMap (Coordinate W k) (Overlap W k j) a) = _
    rw [show transition W j k (algebraMap (Coordinate W k) (Overlap W k j) a) =
      transitionBase W j k a from
        IsLocalization.Away.lift_eq (coord W k j) (transitionBase_isUnit W j k) a]
    exact (overlapDiagonalAlgebra_right W j k a).symm

/-- Each affine restriction of the actual diagonal is a closed immersion. -/
instance integralChartDiagonal_closedImmersion :
    IsClosedImmersion (pullback.mapDesc (integralCurveChart W j) (integralCurveChart W k)
      (integralCurveStructure W)) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (integralChartIntersectionIso W j k).hom, integralChartDiagonal_comparison]
  infer_instance

/-- The global cubic is separated over the base, with no discriminant hypothesis. -/
instance integralCurveStructure_separated : IsSeparated (integralCurveStructure W) := by
  constructor
  change MorphismProperty.diagonal @IsClosedImmersion (integralCurveStructure W)
  rw [← HasAffineProperty.diagonal_iff (P := @IsClosedImmersion)]
  have _ (i : (integralCurveOpenCover W).I₀) :
      IsAffine ((integralCurveOpenCover W).X i) := by
    change IsAffine (chartScheme W i.down)
    infer_instance
  let _ := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  apply AffineTargetMorphismProperty.diagonal_of_openCover_source
    (Q := fun X _ f _ => IsAffine X ∧ Function.Surjective f.appTop)
    (integralCurveStructure W) (integralCurveOpenCover W)
  intro i l
  exact (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp
    (integralChartDiagonal_closedImmersion W i.down l.down)

end FLT.Mazur.WeierstrassIntegralChart
