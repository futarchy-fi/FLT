/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothGeneralizedCurvePointedIso
public import FLT.Mazur.PolygonCompleteOriginalCyclicHom
public import FLT.Mazur.PolygonCompleteSmoothFieldCurve
public import FLT.Mazur.CartesianActionPullback
public import FLT.Mazur.GeneralizedCurveIdentityBaseChange

/-!
# The complete generalized curve retains the original smooth field DR object

The original Cartesian field square and label-zero identity determine a full DR
isomorphism. Rigidity supplies group compatibility from the actual geometry.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
/-- Cartesian comparisons preserve sections with the same original projection. -/
theorem completeCartesianSection_comparison {S T : Scheme} (f : T ⟶ S)
    {X : Over S} {Y : Over T} (p : Y.left ⟶ X.left)
    (hs : IsPullback p Y.hom X.hom f)
    (x : 𝟙_ (Over S) ⟶ X) (y : 𝟙_ (Over T) ⟶ Y)
    (hy : y.left ≫ p = f ≫ x.left) :
    y ≫ (CartesianActionPullback.comparison f p hs).hom =
      GroupSectionBaseChange.pullSection f x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, CartesianActionPullback.comparison_fst,
      GroupSectionBaseChange.section_fst, hy]
  · exact (y ≫ (CartesianActionPullback.comparison f p hs).hom).w.trans
      (GroupSectionBaseChange.pullSection f x).w.symm

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete DR identity is exactly the original zero-labeled section. -/
theorem completeGeneralizedCurve_identity :
    (completeGeneralizedCurve K n h).identitySection.left =
      completeBaseMarking K n h (0 : Fin n) := by
  rw [identitySection, completeGeneralizedCurve_inclusion]
  change (completeOriginalSmoothCyclicPoint K n h 0).left ≫
    (exactVeroneseProjToBase K n h).smoothLocus.ι = _
  rw [completeOriginalSmoothCyclicPoint_inclusion, PolygonPinching.rotateIndex_zero]

variable (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "b" => Spec.map (CommRingCat.ofHom a)
local notation "E" => completeGeneralizedCurve K n h
local notation "F" => completeFieldGeneralizedCurve K n h L a ha p q hs (0 : Fin n)
local notation "c" => CartesianActionPullback.comparison b p hs

/-- The actual Cartesian curve comparison preserves the original DR identity. -/
theorem completeSmoothOriginalCurve_identity :
    (F).identitySection ≫ (c).hom = ((E).baseChange b).identitySection := by
  rw [← pullSection_identity]
  apply completeCartesianSection_comparison
  rw [completeFieldGeneralizedCurve_identity, completeCartesianMarking_fst,
    completeGeneralizedCurve_identity]

/-- The original smooth field DR object retains the proved smoothness of its square. -/
theorem completeSmoothOriginalCurve_smooth : Smooth (F).curve.hom := by
  let _ : SmoothOfRelativeDimension 1 q :=
    completeCartesianField_relativeDimension K n h L a ha p q hs
  exact SmoothOfRelativeDimension.smooth 1 q

include ha in
/-- The complete DR pullback is smooth on every nonzero-parameter field fiber. -/
theorem completeSmoothOriginalPullback_smooth : Smooth ((E).baseChange b).curve.hom := by
  let _ : SmoothOfRelativeDimension 1 ((E).baseChange b).curve.hom :=
    completeCartesianField_relativeDimension K n h L a ha
      (pullback.fst (E).curve.hom b) (pullback.snd (E).curve.hom b)
      (IsPullback.of_hasPullback _ _)
  exact SmoothOfRelativeDimension.smooth 1 _

attribute [local instance] completeSmoothOriginalCurve_smooth

/-- The original smooth field DR object is the actual fiber of the complete DR family. -/
irreducible_def completeSmoothOriginalCurveIso : (F) ≅ (E).baseChange b := by
  let _ := completeSmoothOriginalPullback_smooth K n h L a ha
  exact pointedSmoothIso (F) ((E).baseChange b) c
    (completeSmoothOriginalCurve_identity K n h L a ha p q hs)

/-- The full smooth DR comparison retains the given original complete-family projection. -/
@[reassoc] theorem completeSmoothOriginalCurveIso_fst :
    (completeSmoothOriginalCurveIso K n h L a ha p q hs).hom.curve.left ≫
      pullback.fst (E).curve.hom b = p := by
  rw [completeSmoothOriginalCurveIso_def]
  rw [pointedSmoothIso_curve]
  exact hs.isoPullback_hom_fst

end FLT.Mazur.PolygonInfinitesimalStages
