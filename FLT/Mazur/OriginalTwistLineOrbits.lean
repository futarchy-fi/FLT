/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedLineOriginalTwist
public import FLT.Mazur.TwistedSectionBaseLineNaturality
public import FLT.Mazur.LineSheafDualInvolution
public import FLT.Mazur.CartierAbelRelativeQuotient

/-!
# Original twisting-line isomorphisms on arbitrary bases

Duality identifies retained-line isomorphisms with isomorphisms of the
independently specified original twists carrying their actual sections.
No finiteness or Noetherian condition is imposed on the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve ModuleSheafTensor
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)

/-- Retained orbits use original base-line isomorphisms and the actual original sections. -/
theorem originalTwistLine_rel_iff_iso (s t : TwistedSection f L)
    (hs : SplitLineAffineNeighborhood.LocallySplit (s.toDirectImage f L).map)
    (ht : SplitLineAffineNeighborhood.LocallySplit (t.toDirectImage f L).map) :
    (DualAtlasLineQuotient.lineSetoid _).r
        (originalTwistLine f L s.baseLine s.section_ hs)
        (originalTwistLine f L t.baseLine t.section_ ht) ↔
      ∃ e : s.baseLine.val ≅ t.baseLine.val,
        (map (𝟙 L) ((pullback f).map e.hom)).app ⊤ s.section_ = t.section_ := by
  change (∃ a : moduleSheafDual s.baseLine.val ≅ moduleSheafDual t.baseLine.val,
    a.hom ≫ (t.toDirectImage f L).map = (s.toDirectImage f L).map) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    let e := lineIsoOfDualIso s.baseLine.property t.baseLine.property a.symm
    refine ⟨e, ?_⟩
    apply (twistedSectionPushforwardEquiv f L t.baseLine.property).injective
    rw [twistedSectionPushforwardEquiv_baseLineIso f L e s.baseLine.property,
      lineIsoOfDualIso_dual]
    change a.inv ≫ (s.toDirectImage f L).map = (t.toDirectImage f L).map
    rw [← ha, Iso.inv_hom_id_assoc]
  · rintro ⟨e, he⟩
    refine ⟨(moduleSheafDualIso _ e).symm, ?_⟩
    have h := twistedSectionPushforwardEquiv_baseLineIso f L e
      s.baseLine.property t.baseLine.property s.section_
    rw [he] at h
    change (moduleSheafDualIso _ e).inv ≫
      twistedSectionPushforwardEquiv f L t.baseLine.property t.section_ = _
    rw [h]
    change (moduleSheafDualIso _ e).inv ≫ (moduleSheafDualIso _ e).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
    rfl

end FLT.Mazur.CartierAbel
