/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveCoverRefinement
public import FLT.Mazur.GeneralizedCurveDirectedGluing

/-!
# Full refinement identities supply the gluing equations

Naturality in the full generalized-curve category implies compatibility of
both actual projected map families on the pulled-back directed covers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (C : S.OpenCover) [Category* C.I₀] [C.LocallyDirected]
  {E F : GeneralizedEllipticCurve S}
  (a : ∀ i, E.baseChange (C.f i) ⟶ F.baseChange (C.f i))
  (ha : ∀ {i j : C.I₀} (h : i ⟶ j),
    (coverRefinementIso C E h).hom ≫ baseChangeMap (C.trans h) (a j) =
      a i ≫ (coverRefinementIso C F h).hom)

include ha in
/-- Full naturality gives compatibility of the original curve maps. -/
theorem curve_compatible_of_refinement :
    OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).curve) := by
  intro i j h
  have hh := congrArg (fun z ↦ z.curve.left ≫
    pullback.fst (F.baseChange (C.f j)).curve.hom (C.trans h) ≫
      pullback.fst F.curve.hom (C.f j)) (ha h)
  change ((coverRefinementIso C E h).hom.curve.left ≫
      (baseChangeMap (C.trans h) (a j)).curve.left) ≫ _ =
    ((a i).curve.left ≫ (coverRefinementIso C F h).hom.curve.left) ≫ _ at hh
  simp only [Category.assoc] at hh
  rw [baseChangeMap_fst_assoc, coverRefinementIso_curve_assoc] at hh
  simpa only [coverRefinementIso, baseChangeCompEqIso_curve_fst] using hh

include ha in
/-- Full naturality also retains the original smooth-group maps. -/
theorem group_compatible_of_refinement :
    OverDirectedCoverGluing.Compatible C (fun i ↦ (a i).group) := by
  intro i j h
  have hh := congrArg (fun z ↦ z.group.left ≫
    pullback.fst (F.baseChange (C.f j)).group.hom (C.trans h) ≫
      pullback.fst F.group.hom (C.f j)) (ha h)
  change ((coverRefinementIso C E h).hom.group.left ≫
      (baseChangeMap (C.trans h) (a j)).group.left) ≫ _ =
    ((a i).group.left ≫ (coverRefinementIso C F h).hom.group.left) ≫ _ at hh
  simp only [Category.assoc] at hh
  have hf : (baseChangeMap (C.trans h) (a j)).group.left ≫
      pullback.fst (F.baseChange (C.f j)).group.hom (C.trans h) =
    pullback.fst (E.baseChange (C.f j)).group.hom (C.trans h) ≫ (a j).group.left := by
    simp [baseChangeMap, Over.pullback_map_left]
  rw [reassoc_of% hf, coverRefinementIso_group_assoc] at hh
  simpa only [coverRefinementIso, baseChangeCompEqIso_group_fst] using hh

/-- A family natural for full base change descends to a full global morphism. -/
def glueHomOfRefinement : E ⟶ F :=
  glueHom C a (curve_compatible_of_refinement C a ha) (group_compatible_of_refinement C a ha)

/-- The descended full morphism recovers each given full chart map. -/
theorem glueHomOfRefinement_map (i : C.I₀) :
    baseChangeMap (C.f i) (glueHomOfRefinement C a ha) = a i :=
  glueHom_map C a (curve_compatible_of_refinement C a ha)
    (group_compatible_of_refinement C a ha) i

end FLT.Mazur.GeneralizedEllipticCurve
