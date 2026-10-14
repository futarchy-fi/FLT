/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericTranslation
public import FLT.Mazur.PolygonCompleteIdentityChartAtlas
public import FLT.Mazur.GroupSchemePointAdjunction

/-!
# Original chart operations on arbitrary generic test schemes

The actual pullback adjunction preserves the identity-group operations.
The projection formulas identify each original chart with translation by
its original cyclic section in the independently compared generic group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation GroupSchemePointAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation translation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "H" => Functor.obj (Functor.mapCommGrp (Over.pullback s)) (G)
local notation "u" => Scheme.Opens.ι (completePointIdentityOpen K n h (0 : Fin n))
local notation "π" => exactVeroneseProjToBase K n h
variable {T : Over (Spec (.of L))}
local notation "e" => pointsEquiv s (completePointOriginalBaseGroup K n h (0 : Fin n)) T
attribute [local instance] exactVeroneseProjToBase_lfp

/-- Projection to the original total space detects generic group-valued morphisms. -/
theorem completeGenericPoint_ext (x y : T ⟶ (H).X)
    (he : x.left ≫ pullback.fst (G).X.hom s ≫ u =
      y.left ≫ pullback.fst (G).X.hom s ≫ u) : x = y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply (cancel_mono u).mp
    simpa only [Category.assoc] using he
  · exact x.w.trans y.w.symm

/-- Evaluating an original chart is precisely translation in the actual generic group. -/
theorem completeGenericChart_evaluation (b : ZMod n) (x : T ⟶ (H).X) :
    (((e).symm x) ≫ completeIdentityChart K n h 0 b).left ≫ (π).smoothLocus.ι =
      (x ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs b)).left ≫
        pullback.fst (G).X.hom s ≫ u := by
  change ((e).symm x).left ≫ (completeIdentityChart K n h 0 b).left ≫
    (π).smoothLocus.ι = x.left ≫
      (translation (completePointGenericCyclicPoint K n h L a ha p q hs b)).left ≫
        pullback.fst (G).X.hom s ≫ u
  rw [completeIdentityChart_inclusion, pointsEquiv_symm_left,
    completePointGenericTranslation_original, Category.assoc]

/-- Two original chart presentations agree exactly when their translated generic points agree. -/
theorem completeGenericChart_eq_iff (b c : ZMod n) (x y : T ⟶ (H).X) :
    (e).symm x ≫ completeIdentityChart K n h 0 b =
      (e).symm y ≫ completeIdentityChart K n h 0 c ↔
        x ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs b) =
          y ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs c) := by
  constructor
  · intro he
    apply completeGenericPoint_ext K n h L a
    rw [← completeGenericChart_evaluation K n h L a ha p q hs,
      ← completeGenericChart_evaluation K n h L a ha p q hs, he]
  · intro he
    apply Over.OverMorphism.ext
    apply (cancel_mono (π).smoothLocus.ι).mp
    rw [completeGenericChart_evaluation K n h L a ha p q hs,
      completeGenericChart_evaluation K n h L a ha p q hs, he]

end FLT.Mazur.PolygonInfinitesimalStages
