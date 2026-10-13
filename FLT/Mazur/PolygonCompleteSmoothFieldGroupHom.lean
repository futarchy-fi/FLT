/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothFieldCurve
public import FLT.Mazur.PolygonCompleteCartesianRefinement
public import FLT.Mazur.ProperSmoothRelativePointedGroupHom
public import FLT.Mazur.NodalFamilyGeometricConnected
public import FLT.Mazur.SmoothConnectedCurveGeometricIntegral

/-!
# Original pointed comparisons preserve the constructed smooth field laws

Rigidity identifies the group laws on independently specified original smooth
field squares. The actual complete-family refinement is therefore a group
homomorphism, with no group compatibility assumption on the refinement.
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
  {Y Z : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
  (p' : Z ⟶ exactVeroneseProj K n h) (q' : Z ⟶ Spec (.of L))
  (ht : IsPullback p' q' (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)

include ha hs in
/-- Original smooth field curves are geometrically integral over the original field. -/
theorem completeField_geometricallyIntegral : GeometricallyIntegral q := by
  let _ := completeCartesianField_relativeDimension K n h L a ha p q hs
  have hc := (completeField_classifiedGenusOneFamily K n h L a p q hs).toNodalFamilyCore
  let _ := hc.fibers.geometricallyConnected
  exact smoothConnectedCurve_geometricallyIntegral q

/-- An actual map preserving the original chosen markings preserves the constructed group laws. -/
theorem completeFieldPointedMap_isMonHom (i j : Fin n) (f : Over.mk q ⟶ Over.mk q')
    (hf : completeCartesianMarking K n h s p q hs i ≫ f.left =
      completeCartesianMarking K n h s p' q' ht j) :
    let _ := completeFieldCommGrp K n h L a ha p q hs i
    let _ := completeFieldCommGrp K n h L a ha p' q' ht j
    IsMonHom f := by
  let _ := completeFieldCommGrp K n h L a ha p q hs i
  let _ := completeFieldCommGrp K n h L a ha p' q' ht j
  let _ : SmoothOfRelativeDimension 1 (Over.mk q).hom :=
    completeCartesianField_relativeDimension K n h L a ha p q hs
  let _ : GeometricallyIntegral (Over.mk q).hom :=
    completeField_geometricallyIntegral K n h L a ha p q hs
  let _ : IsProper (Over.mk q).hom :=
    (completeField_classifiedGenusOneFamily K n h L a p q hs).family.1
  let _ : IsProper (Over.mk q').hom :=
    (completeField_classifiedGenusOneFamily K n h L a p' q' ht).family.1
  let _ : LocallyOfFinitePresentation (Over.mk q').hom :=
    (completeField_classifiedGenusOneFamily K n h L a p' q' ht).family.2.2
  apply properSmoothRelative_isMonHom_of_one (Over.mk q) (Over.mk q') f
  apply Over.OverMorphism.ext
  simpa only [Over.comp_left, completeFieldCommGrp_identity] using hf

/-- The unique actual refinement over the unchanged field, as a relative curve morphism. -/
def completeFieldRefinement : Over.mk q' ⟶ Over.mk q :=
  Over.homMk (completeCartesianRefinement K n h s p q hs s p' q' ht (𝟙 _) (by simp))
    (by
      change _ ≫ q = q'
      exact (completeCartesianRefinement_snd K n h s p q hs s p' q' ht
        (𝟙 _) (by simp)).trans (Category.comp_id q'))

/-- The actual refinement preserves the full group law with the same original identity label. -/
theorem completeFieldRefinement_isMonHom (i : Fin n) :
    let _ := completeFieldCommGrp K n h L a ha p' q' ht i
    let _ := completeFieldCommGrp K n h L a ha p q hs i
    IsMonHom (completeFieldRefinement K n h L a p q hs p' q' ht) := by
  apply completeFieldPointedMap_isMonHom K n h L a ha p' q' ht p q hs i i
  exact (completeCartesianRefinement_marking K n h s p q hs s p' q' ht
    (𝟙 _) (by simp) i).trans (Category.id_comp _)

end FLT.Mazur.PolygonInfinitesimalStages
