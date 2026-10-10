/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionNormalizedRefinement

/-!
# Genuine normalized point squares on arbitrary common affine refinements

Normalized expressions of the section in two parent charts determine the
actual dual transition square on every common affine open. The auxiliary
atlas point is constructed using an inherited free frame, then eliminated.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionChartPoints
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas NormalizedSectionLine
open FiniteFreeChartTransitions ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ LocallyFreeDualProjectiveAtlas.space M hM)
variable (hs : s ≫ projection M hM = 𝟙 X)

/-- A normalized expression in a parent chart determines the actual refined chart point. -/
lemma normalized_local_point {i j : Index M} (h : i ≤ j) (k : coordinates M j)
    (L : Chart Γ(i.val.toScheme, ⊤) (coordinates M j) k)
    (hp : X.homOfLE h ≫ point M hM s hs j =
      affineSectionLinePoint (X.homOfLE h).appTop.hom k L) :
    point M hM s hs i ≫
        (dualProjectiveTransition M le_rfl h (chart M i) (chart M j)).hom =
      affineSectionLinePoint (.id _) k L := by
  apply (cancel_mono (coefficientMap (X.homOfLE h).appTop.hom (coordinates M j))).mp
  rw [Category.assoc]
  change point M hM s hs i ≫ dualChartInclusion M h (chart M i) (chart M j) = _
  rw [← point_refinement, hp, affineSectionLinePoint_coefficientMap, RingHom.id_comp]

/-- Normalized local expressions of one section satisfy the genuine common-overlap square. -/
lemma normalized_common_point (i j : Index M) {W : X.Opens} [IsAffine W.toScheme]
    (hU : W ≤ i.val) (hV : W ≤ j.val) (a : coordinates M i) (b : coordinates M j)
    (L : Chart Γ(W.toScheme, ⊤) (coordinates M i) a)
    (N : Chart Γ(W.toScheme, ⊤) (coordinates M j) b)
    (hi : X.homOfLE hU ≫ point M hM s hs i =
      affineSectionLinePoint (X.homOfLE hU).appTop.hom a L)
    (hj : X.homOfLE hV ≫ point M hM s hs j =
      affineSectionLinePoint (X.homOfLE hV).appTop.hom b N) :
    sectionLinePoint Γ(W.toScheme, ⊤) (coordinates M i) (.id _) a L ≫
        (dualProjectiveTransition M hU hV (chart M i) (chart M j)).hom =
      sectionLinePoint Γ(W.toScheme, ⊤) (coordinates M j) (.id _) b N := by
  let w : Index M := ⟨W, ‹IsAffine W.toScheme›, coordinates M i, inferInstance,
    ⟨refineChart M hU (chart M i)⟩⟩
  have hwi : w ≤ i := hU
  have hwj : w ≤ j := hV
  have hi' := normalized_local_point M hM s hs hwi a L hi
  have hj' := normalized_local_point M hM s hs hwj b N hj
  apply (cancel_epi W.toScheme.isoSpec.hom).mp
  rw [← Category.assoc]
  change affineSectionLinePoint (.id _) a L ≫ _ = affineSectionLinePoint (.id _) b N
  rw [← hi', Category.assoc, ← Iso.trans_hom,
    dualProjectiveTransition_cocycle, hj']

end FLT.Mazur.DualAtlasSectionChartPoints
