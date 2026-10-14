/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkedProjectivePoints
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# A group on each original smooth field fiber with its original marked identity

The constructed nonsingular cubic supplies its proved group law. The original
projective comparison already takes the chosen mark to infinity. Transport its
law to the entire original smooth curve, with no input group law on that curve.
This is a field-fiber construction only.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a))) (i : Fin n)
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "W" => completeCartesianPointWeierstrass K n h L s p q hs i
local notation "hW" => (completeCartesianPointWeierstrass_isElliptic K n h L a ha p q hs i)

/-- The original marked section as a point of the original curve over its field. -/
def completeFieldMarkedPoint : 𝟙_ (Over (Spec (.of L))) ⟶ Over.mk q :=
  Over.homMk (completeCartesianMarking K n h s p q hs i)
    (completeCartesianMarking_snd K n h s p q hs i)

/-- The constructed projective cubic comparison is over the unchanged original field. -/
def completeFieldCubicOverIso : Over.mk q ≅ integralCurveOver W :=
  Over.isoMk (completeCartesianPointProjectiveIso K n h L a ha p q hs i)
    (completeCartesianPointProjectiveIso_over K n h L a ha p q hs i)

/-- The established commutative law on the actually constructed cubic. -/
abbrev completeFieldCubicCommGrp : CommGrpObj (integralCurveOver W) :=
  integralCurveCommGrpObj W (by let _ := hW; exact WeierstrassCurve.isUnit_Δ W)

local notation "cg" => completeFieldCubicCommGrp K n h L a ha p q hs i

/-- The actual projective comparison sends the original marking to the cubic identity. -/
theorem completeFieldCubicOverIso_marking :
    let _ := cg
    completeFieldMarkedPoint K n h L a p q hs i ≫
      (completeFieldCubicOverIso K n h L a ha p q hs i).hom = 1 := by
  let _ := cg
  apply Over.OverMorphism.ext
  change completeCartesianMarking K n h s p q hs i ≫
    completeCartesianPointToProjective K n h L a ha p q hs i = integralCurveZero W
  exact completeCartesianPointToProjective_marking K n h L a ha p q hs i

/-- The entire original smooth field curve carries a constructed commutative group law. -/
abbrev completeFieldCommGrp : CommGrpObj (Over.mk q) := by
  let _ := cg
  refine
    { __ := GrpObj.ofIso (completeFieldCubicOverIso K n h L a ha p q hs i).symm
      mul_comm := ?_ }
  change (β_ _ _).hom ≫
    ((completeFieldCubicOverIso K n h L a ha p q hs i).hom ⊗ₘ
      (completeFieldCubicOverIso K n h L a ha p q hs i).hom) ≫
        MonObj.mul ≫ (completeFieldCubicOverIso K n h L a ha p q hs i).inv = _
  rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
  rfl

/-- The identity of the constructed full group is exactly the original marked section. -/
theorem completeFieldCommGrp_identity :
    let _ := completeFieldCommGrp K n h L a ha p q hs i
    (η[Over.mk q]).left = completeCartesianMarking K n h s p q hs i := by
  let _ := cg
  let _ := completeFieldCommGrp K n h L a ha p q hs i
  have he : (1 : 𝟙_ (Over (Spec (.of L))) ⟶ Over.mk q) =
      completeFieldMarkedPoint K n h L a p q hs i := by
    apply (cancel_mono (completeFieldCubicOverIso K n h L a ha p q hs i).hom).mp
    rw [completeFieldCubicOverIso_marking]
    change η[integralCurveOver W] ≫
      (completeFieldCubicOverIso K n h L a ha p q hs i).inv ≫
        (completeFieldCubicOverIso K n h L a ha p q hs i).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
    rfl
  exact congrArg Over.Hom.left he

end FLT.Mazur.PolygonInfinitesimalStages
