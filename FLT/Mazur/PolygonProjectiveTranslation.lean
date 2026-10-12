/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveFixedPointFree
public import FLT.Mazur.PolygonProjectiveRotationNormalization
public import FLT.Mazur.WeierstrassFixedPointTranslation

/-!
# Original projective rotations are actual elliptic translations

Every nonzero rotation has no geometric fixed points, so its normalized
automorphism is identity. The zero label is handled by the proved action law.
The result retains the original field, chosen square, cubic and infinity image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeProjectiveRotationIso translation normalizedIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs

/-- The actual original projective action is translation by its actual infinity image. -/
theorem completeProjectiveRotation_eq_translation (i : Fin n) (b : ZMod n) :
    let _ := integralCurveCommGrpObj (W i) (by
      let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
      exact WeierstrassCurve.isUnit_Δ _)
    let e := curveAutomorphismOverIso (W i)
      (completeProjectiveRotationIso K n h L a ha p q hs i b)
      (completeProjectiveRotationIso_over K n h L a ha p q hs i b)
    e.hom = translation ((1 : 𝟙_ (Over (Spec (.of L))) ⟶ integralCurveOver (W i)) ≫ e.hom) := by
  let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  let _ := integralCurveCommGrpObj (W i) (WeierstrassCurve.isUnit_Δ _)
  dsimp only
  by_cases hb : b = 0
  · subst b
    have he : (curveAutomorphismOverIso (W i)
        (completeProjectiveRotationIso K n h L a ha p q hs i 0)
        (completeProjectiveRotationIso_over K n h L a ha p q hs i 0)).hom = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact completeProjectiveRotationIso_zero K n h L a ha p q hs i
    rw [he, Category.comp_id, translation_one]
  · let _ : IsProper (integralCurveOver (W i)).hom :=
      inferInstanceAs (IsProper (integralCurveStructure (W i)))
    let _ : GeometricallyIntegral (integralCurveOver (W i)).hom :=
      inferInstanceAs (GeometricallyIntegral (integralCurveStructure (W i)))
    let _ : SmoothOfRelativeDimension 1 (integralCurveOver (W i)).hom :=
      integralCurveStructure_smooth_dimension (W i) (WeierstrassCurve.isUnit_Δ _)
    apply geometricFixedPointFree_eq_translation
    intro T _ t
    exact completeProjectiveRotation_comp_ne K n h L a ha p q hs i t b hb

/-- The originally constructed residual group automorphism is the identity on its cubic. -/
theorem completeProjectiveRotationGroupPart_eq_id (i : Fin n) (b : ZMod n) :
    (completeProjectiveRotationGroupPart K n h L a ha p q hs i b).hom.hom.hom.hom.left =
      𝟙 _ := by
  let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  let _ := integralCurveCommGrpObj (W i) (WeierstrassCurve.isUnit_Δ _)
  rw [completeProjectiveRotationGroupPart_hom]
  exact congrArg Over.Hom.left ((eq_translation_iff _).mp
    (completeProjectiveRotation_eq_translation K n h L a ha p q hs i b))

end FLT.Mazur.PolygonInfinitesimalStages
