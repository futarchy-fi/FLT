/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineMorphismSectionTransport
public import FLT.Mazur.LineMorphismTensorStage

/-!
# Original stage restrictions of morphism sections

A commutative original-stage square gives the corresponding compatible
section of the tensor-dual morphism line, with no new choices.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor lineMorphismTensorPullbackIso
variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) {L : S.Modules} (hL : LocallyFreeRankOne L) (M : S.Modules)

/-- The original stage transition on the tensor-dual line representing morphisms. -/
def lineMorphismSectionTransition :
    (pullback r).obj (tensor ((pullback q).obj M)
      (moduleSheafDual ((pullback q).obj L))) ⟶
        tensor ((pullback p).obj M) (moduleSheafDual ((pullback p).obj L)) :=
  (lineMorphismTensorPullbackIso (hL.pullback q) ((pullback q).obj M) r).hom ≫
    map (pullbackStageIso p q r h M).hom
      (moduleSheafDualIso _ (pullbackStageIso p q r h L)).inv

/-- A commuting original-stage square gives compatible actual tensor-dual sections. -/
theorem lineMorphismSectionTransition_apply
    (a : (pullback q).obj L ⟶ (pullback q).obj M)
    (b : (pullback p).obj L ⟶ (pullback p).obj M)
    (hab : (pullback r).map a ≫ (pullbackStageIso p q r h M).hom =
      (pullbackStageIso p q r h L).hom ≫ b) :
    (lineMorphismSectionTransition p q r h hL M).app ⊤
        (pullGlobal r _ (lineMorphismSectionEquiv (hL.pullback q) _ a)) =
      lineMorphismSectionEquiv (hL.pullback p) _ b := by
  change (map (pullbackStageIso p q r h M).hom
    (moduleSheafDualIso _ (pullbackStageIso p q r h L)).inv).app ⊤
      ((lineMorphismTensorPullbackIso (hL.pullback q) ((pullback q).obj M) r).hom.app ⊤
        (pullGlobal r _ (lineMorphismSectionEquiv (hL.pullback q) _ a))) = _
  rw [lineMorphismSectionEquiv_pullback,
    ← lineMorphismSectionEquiv_transport ((hL.pullback q).pullback r) (hL.pullback p)]
  rw [hab, Iso.inv_hom_id_assoc]

end FLT.Mazur.FCurve
