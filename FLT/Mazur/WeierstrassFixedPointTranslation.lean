/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCurveFixedPointTranslation
public import FLT.Mazur.GeometricFixedPointTranslation
public import FLT.Mazur.WeierstrassAutomorphismNormalization
public import FLT.Mazur.WeierstrassSmoothFiberCore

/-!
# Fixed-point-free cubic automorphisms have trivial normalized part

The actual smooth proper integral cubic is a group curve of dimension one.
The geometric fixed-point argument identifies its normalized automorphism
with the identity over its original field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] GroupObjectPointTranslation.translation
  GroupObjectPointTranslation.normalizedIso
variable {K : Type} [Field K] (W : WeierstrassCurve K)
  (hΔ : IsUnit W.Δ) (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)

/-- No fixed rational point forces the actual normalized elliptic automorphism to be identity. -/
theorem normalizedCurveIso_eq_id_of_fixedPointFree [IsAlgClosed K]
    (hf : ∀ q : Spec (.of K) ⟶ integralCurve W,
      q ≫ integralCurveStructure W = 𝟙 _ → q ≫ e.hom ≠ q) :
    (normalizedCurveIso W hΔ e hb).hom = 𝟙 _ := by
  let _ := integralCurveCommGrpObj W hΔ
  let _ := integralCurveStructure_smooth_dimension W hΔ
  let _ : IsIntegral (integralCurveOver W).left :=
    inferInstanceAs (IsIntegral (integralCurve W))
  let _ : IsProper (integralCurveOver W).hom :=
    inferInstanceAs (IsProper (integralCurveStructure W))
  have hd : topologicalKrullDim (integralCurveOver W).left ≤ 1 :=
    le_of_eq (FCurve.smoothCurveDimension (integralCurveStructure W)
      inferInstance inferInstance)
  have he := GroupObjectPointTranslation.fixedPointFree_eq_translation hd
    (curveAutomorphismOverIso W e hb) (by
      intro q hq
      exact hf q.left q.w (congrArg Over.Hom.left hq))
  have hn := (GroupObjectPointTranslation.eq_translation_iff
    (curveAutomorphismOverIso W e hb)).mp he
  exact congrArg Over.Hom.left hn

/-- Geometric fixed-point freeness kills the normalized part over the original field. -/
theorem normalizedCurveIso_eq_id_of_geometricFixedPointFree
    (hf : ∀ (T : Scheme) [Nonempty T] (q : T ⟶ integralCurve W), q ≫ e.hom ≠ q) :
    (normalizedCurveIso W hΔ e hb).hom = 𝟙 _ := by
  let _ := integralCurveCommGrpObj W hΔ
  let _ : IsProper (integralCurveOver W).hom :=
    inferInstanceAs (IsProper (integralCurveStructure W))
  let _ : GeometricallyIntegral (integralCurveOver W).hom :=
    inferInstanceAs (GeometricallyIntegral (integralCurveStructure W))
  let _ : SmoothOfRelativeDimension 1 (integralCurveOver W).hom :=
    integralCurveStructure_smooth_dimension W hΔ
  have he := GroupObjectPointTranslation.geometricFixedPointFree_eq_translation
    (curveAutomorphismOverIso W e hb) hf
  have hn := (GroupObjectPointTranslation.eq_translation_iff
    (curveAutomorphismOverIso W e hb)).mp he
  exact congrArg Over.Hom.left hn

end FLT.Mazur.WeierstrassIntegralChart
