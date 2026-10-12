/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveTranslation

/-!
# The original cyclic markings respect the elliptic group law

The proved translation action identifies rotation of every retained marking
with multiplication by the shifted infinity marking in the actual point group.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart GroupObjectPointTranslation PolygonPinching
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
local notation "P" => completeCartesianProjectiveMarkedPoint K n h L a ha p q hs

/-- Multiplication by a shifted infinity marking rotates every original marked point. -/
theorem completeProjectiveMarkedPoint_mul (i j : Fin n) (b : ZMod n) :
    P i (rotateIndex b i) * P i j = P i (rotateIndex b j) := by
  let _ := completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i
  let _ := integralCurveCommGrpObj (W i) (WeierstrassCurve.isUnit_Δ _)
  let e := curveAutomorphismOverIso (W i)
    (completeProjectiveRotationIso K n h L a ha p q hs i b)
    (completeProjectiveRotationIso_over K n h L a ha p q hs i b)
  have he := completeProjectiveRotation_eq_translation K n h L a ha p q hs i b
  have horbit (k : Fin n) : P i k ≫ e.hom = P i (rotateIndex b k) := by
    apply Over.OverMorphism.ext
    exact completeProjectiveMarkedPoint_rotation K n h L a ha p q hs i k b
  have hp : (toUnit (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L L))))) ≫
      ((1 : 𝟙_ (Over (Spec (.of L))) ⟶ integralCurveOver (W i)) ≫ e.hom) =
        P i (rotateIndex b i) := by
    rw [← Category.assoc, MonObj.comp_one]
    rw [← completeCartesianProjectiveMarkedPoint_self K n h L a ha p q hs i]
    exact horbit i
  have hr := horbit j
  rw [he, comp_translation, hp] at hr
  exact hr

/-- The shifted original labels add according to their actual elliptic point multiplication. -/
theorem completeProjectiveMarkedPoint_add (i : Fin n) (b c : ZMod n) :
    P i (rotateIndex (b + c) i) = P i (rotateIndex b i) * P i (rotateIndex c i) := by
  rw [add_comm b c, rotateIndex_add]
  exact (completeProjectiveMarkedPoint_mul K n h L a ha p q hs i (rotateIndex c i) b).symm

end FLT.Mazur.PolygonInfinitesimalStages
