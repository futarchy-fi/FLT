/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonProjectiveAuxiliaryMarking

/-!
# Original rotation on every auxiliary and cyclic marked section

The proved translation law acts on every test-scheme section, not just the
original field points. On the full marking it shifts precisely the cyclic
factor and retains the auxiliary label.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart UniversalWeierstrass GroupObjectPointTranslation PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeProjectiveRotationIso translation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "G" => completeProjectiveGroup K n h L a ha p q hs
local notation "W" => completeCartesianPointWeierstrass K n h L
  (Spec.map (CommRingCat.ofHom a)) p q hs
local notation "P" => completeCartesianProjectiveMarkedPoint K n h L a ha p q hs

/-- The original rotation on the constructed group carrier need not fix zero. -/
def completeProjectiveRotationOverIso (i : Fin n) (b : ZMod n) : (G i).X ≅ (G i).X :=
  curveAutomorphismOverIso (W i) (completeProjectiveRotationIso K n h L a ha p q hs i b)
    (completeProjectiveRotationIso_over K n h L a ha p q hs i b)

/-- The original rotation is translation on sections over every test scheme. -/
theorem completeProjectiveRotation_test (i : Fin n) (b : ZMod n)
    {T : Over (Spec (.of L))} (x : T ⟶ (G i).X) :
    x ≫ (completeProjectiveRotationOverIso K n h L a ha p q hs i b).hom =
      (completeProjectiveFieldMap L T ≫ P i (rotateIndex b i) : T ⟶ (G i).X) * x := by
  let e := completeProjectiveRotationOverIso K n h L a ha p q hs i b
  have he : e.hom = translation ((1 : 𝟙_ (Over (Spec (.of L))) ⟶ (G i).X) ≫ e.hom) :=
    completeProjectiveRotation_eq_translation K n h L a ha p q hs i b
  let F := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L L)))
  have hp : toUnit F ≫ ((1 : 𝟙_ (Over (Spec (.of L))) ⟶ (G i).X) ≫ e.hom) =
      (P i (rotateIndex b i) : F ⟶ (G i).X) := by
    rw [← Category.assoc, MonObj.comp_one]
    rw [← completeCartesianProjectiveMarkedPoint_self K n h L a ha p q hs i]
    apply Over.OverMorphism.ext
    exact completeProjectiveMarkedPoint_rotation K n h L a ha p q hs i i b
  have ht : toUnit T ≫ ((1 : 𝟙_ (Over (Spec (.of L))) ⟶ (G i).X) ≫ e.hom) =
      completeProjectiveFieldMap L T ≫ P i (rotateIndex b i) := by
    have hh := congrArg (fun z : F ⟶ (G i).X ↦ completeProjectiveFieldMap L T ≫ z) hp
    rw [← Category.assoc (completeProjectiveFieldMap L T) (toUnit F), comp_toUnit] at hh
    exact hh
  change x ≫ e.hom = _
  rw [he, comp_translation, ht]

/-- Every auxiliary section rotates by shifting only its original cyclic label. -/
theorem completeProjectiveFullMarking_rotation (i : Fin n) (b : ZMod n)
    {T : Over (Spec (.of L))}
    (f : T ⟶ completeProjectiveAuxiliaryScheme K n h L a ha p q hs i) (c : CyclicLabels n) :
    completeProjectiveFullMarking K n h L a ha p q hs i f c ≫
      (completeProjectiveRotationOverIso K n h L a ha p q hs i b).hom =
        completeProjectiveFullMarking K n h L a ha p q hs i f
          ((1, Multiplicative.ofAdd b) * c) := by
  rw [completeProjectiveRotation_test, map_mul]
  have hc : completeProjectiveFullMarking K n h L a ha p q hs i f
      (1, Multiplicative.ofAdd b) =
        (completeProjectiveFieldMap L T ≫ P i (rotateIndex b i) : T ⟶ (G i).X) := by
    rw [completeProjectiveFullMarking_apply, map_one, one_mul]
    rfl
  rw [hc]

end FLT.Mazur.PolygonInfinitesimalStages
