/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldGroup
public import FLT.Mazur.PolygonCompleteGenusOneFamily
public import FLT.Mazur.ClassifiedGenusOneCartesian
public import FLT.Mazur.GeneralizedEllipticCurve

/-!
# The original smooth field square as a generalized elliptic curve

The original entire curve, its marked group identity and its multiplication
assemble into a full DR object. The geometric rotation condition follows from
smoothness after every field extension. No boundary group extension is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

include hs in
/-- The original field square retains the complete classified genus-one family. -/
theorem completeField_classifiedGenusOneFamily : ClassifiedGenusOneFamily q :=
  (exactVeroneseProjToBase_classifiedGenusOneFamily K n h).of_isPullback hs

include ha in
/-- Smoothness makes the original smooth-open inclusion an isomorphism. -/
theorem completeFieldSmoothInclusion_isIso :
    let _ : LocallyOfFinitePresentation (Over.mk q).hom :=
      (completeField_classifiedGenusOneFamily K n h L a p q hs).family.2.2
    IsIso (curveSmoothInclusion (Over.mk q)) := by
  let _ : LocallyOfFinitePresentation (Over.mk q).hom :=
    (completeField_classifiedGenusOneFamily K n h L a p q hs).family.2.2
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have hi : IsIso q.smoothLocus.ι := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    exact Y.topIso.isIso_hom
  have : IsIso ((Over.forget (Spec (.of L))).map
      (curveSmoothInclusion (Over.mk q))) := hi
  exact isIso_of_reflects_iso _ (Over.forget (Spec (.of L)))

/-- Identify the full original group carrier with its actual smooth open. -/
def completeFieldSmoothIso :
    let _ : LocallyOfFinitePresentation (Over.mk q).hom :=
      (completeField_classifiedGenusOneFamily K n h L a p q hs).family.2.2
    Over.mk q ≅ curveSmoothOpen (Over.mk q) := by
  let _ : LocallyOfFinitePresentation (Over.mk q).hom :=
    (completeField_classifiedGenusOneFamily K n h L a p q hs).family.2.2
  let _ := completeFieldSmoothInclusion_isIso K n h L a ha p q hs
  exact (asIso (curveSmoothInclusion (Over.mk q))).symm

/-- The original smooth inclusion is unchanged by the comparison. -/
@[reassoc] theorem completeFieldSmoothIso_inclusion :
    let _ : LocallyOfFinitePresentation (Over.mk q).hom :=
      (completeField_classifiedGenusOneFamily K n h L a p q hs).family.2.2
    (completeFieldSmoothIso K n h L a ha p q hs).hom ≫
      curveSmoothInclusion (Over.mk q) = 𝟙 _ :=
  (completeFieldSmoothIso K n h L a ha p q hs).hom_inv_id

/-- The full original smooth field curve, with the chosen original marking as identity. -/
def completeFieldGeneralizedCurve (i : Fin n) : GeneralizedEllipticCurve (Spec (.of L)) := by
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let _ := completeFieldCommGrp K n h L a ha p q hs i
  refine
    { curve := Over.mk q
      family := completeField_classifiedGenusOneFamily K n h L a p q hs
      group := Over.mk q
      smoothIso := completeFieldSmoothIso K n h L a ha p q hs
      act := μ[Over.mk q]
      unit_act := MonObj.one_mul _
      assoc_act := MonObj.mul_assoc _
      restriction := ?_
      rotations := ?_ }
  · rw [completeFieldSmoothIso_inclusion, whiskerLeft_id, Category.id_comp, Category.comp_id]
  · intro M _ _ g hg
    exact hg (inferInstanceAs (Smooth (pullback.snd q g))) |>.elim

/-- The DR inclusion is the identity of the original entire smooth curve. -/
theorem completeFieldGeneralizedCurve_inclusion (i : Fin n) :
    (completeFieldGeneralizedCurve K n h L a ha p q hs i).inclusion = 𝟙 _ :=
  completeFieldSmoothIso_inclusion K n h L a ha p q hs

/-- The DR identity retains precisely the original label, including label zero. -/
theorem completeFieldGeneralizedCurve_identity (i : Fin n) :
    (completeFieldGeneralizedCurve K n h L a ha p q hs i).identitySection.left =
      completeCartesianMarking K n h (Spec.map (CommRingCat.ofHom a)) p q hs i := by
  rw [GeneralizedEllipticCurve.identitySection, completeFieldGeneralizedCurve_inclusion,
    Category.comp_id]
  exact completeFieldCommGrp_identity K n h L a ha p q hs i

end FLT.Mazur.PolygonInfinitesimalStages
