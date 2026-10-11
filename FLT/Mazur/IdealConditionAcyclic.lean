/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionConditionAcyclic
public import FLT.Mazur.LineStructureProjection
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# Imposing the full closed-subscheme vanishing condition

The ideal tensor is the actual kernel of restriction of a line to a closed
subscheme. Surjectivity of the original pullback on global sections therefore
preserves acyclicity when tensoring with that ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open Scheme.Modules ModuleSheafTensor ModuleSheafTensorCurrying

variable {X : Scheme} (I : X.IdealSheafData) {L : X.Modules}

/-- The exact ideal quotient sequence tensored with the original line. -/
def idealLineCondition : ShortComplex X.Modules :=
  (idealQuotientComplex I).map (tensoring L)

/-- Invertibility of the coefficient line preserves the actual ideal sequence. -/
theorem idealLineCondition_shortExact (hL : LocallyFreeRankOne L) :
    (idealLineCondition I (L := L)).ShortExact :=
  ModuleLineTensorExact.shortExact _ (idealQuotientComplex_shortExact I) L hL

/-- The quotient comparison takes ideal reduction to actual section pullback. -/
theorem idealLineCondition_projection (hL : LocallyFreeRankOne L) :
    (idealLineCondition I (L := L)).g ≫
        (LineStructureProjection.iso I.subschemeι L hL).hom =
      (leftUnitor L).hom ≫ (pullbackPushforwardAdjunction I.subschemeι).unit.app L := by
  change ModuleSheafTensor.map (idealQuotientMap I) (𝟙 L) ≫ _ = _
  apply ModuleSheafTensor.hom_ext
  intro U r l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply]
  erw [LineStructureProjection.iso_pure, leftUnitor_pure]
  exact ((((pullbackPushforwardAdjunction I.subschemeι).unit.app L).val.app
    (Opposite.op U)).hom.map_smul r l).symm

/-- Surjectivity of pullback is surjectivity of the actual tensor-quotient map. -/
theorem idealLineCondition_surjective (hL : LocallyFreeRankOne L)
    (hs : Function.Surjective (pullGlobal I.subschemeι L)) :
    Function.Surjective ((idealLineCondition I (L := L)).g.app ⊤) := by
  let e := LineStructureProjection.iso I.subschemeι L hL
  intro t
  obtain ⟨s, hs⟩ := hs (e.hom.app ⊤ t)
  refine ⟨(leftUnitor L).inv.app ⊤ s, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  have h := congrArg (fun a ↦ a.app ⊤ ((leftUnitor L).inv.app ⊤ s))
    (idealLineCondition_projection I hL)
  have hu : (leftUnitor L).hom.app ⊤ ((leftUnitor L).inv.app ⊤ s) = s :=
    ConcreteCategory.congr_hom
      (congrArg (fun a ↦ a.app ⊤) (leftUnitor L).inv_hom_id) s
  change e.hom.app ⊤ ((idealLineCondition I (L := L)).g.app ⊤
    ((leftUnitor L).inv.app ⊤ s)) = _ at h
  exact h.trans ((congrArg (pullGlobal I.subschemeι L) hu).trans hs)

/-- A surjective restriction to the full subscheme preserves H¹ vanishing. -/
theorem idealLine_h1_vanishing_of_pullGlobal_surjective {k : Type} [Field k]
    (f : X ⟶ Spec (.of k)) (hL : LocallyFreeRankOne L)
    [Subsingleton (ModuleScalarH f L 1)]
    (hs : Function.Surjective (pullGlobal I.subschemeι L)) :
    Subsingleton (ModuleScalarH f (tensor (idealModule I) L) 1) := by
  let _ : Subsingleton (ModuleH L 1) :=
    inferInstanceAs (Subsingleton (ModuleScalarH f L 1))
  let hz : Subsingleton (ModuleH (tensor (structureModule X) L) 1) :=
    moduleH_subsingleton_of_iso (leftUnitor L) 1
  let _ : Subsingleton (ModuleScalarH f (idealLineCondition I (L := L)).X₂ 1) := hz
  exact kernel_h1_vanishing_of_sections_surjective f (idealLineCondition I)
    (idealLineCondition_shortExact I hL) (idealLineCondition_surjective I hL hs)

end FLT.Mazur.FCurve
