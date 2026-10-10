/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTwistLineOrbits

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

/-- The original twist-isomorphism relation, retaining the actual original section equation. -/
@[irreducible] def originalTwistIsoRelation (s t : TwistedSection f L) : Prop :=
  ∃ e : s.baseLine.val ≅ t.baseLine.val,
    (map (𝟙 L) ((pullback f).map e.hom)).app ⊤ s.section_ = t.section_

/-- Dual retained-line orbits are exactly the sealed original twisting-line relation. -/
lemma originalTwistLine_rel_iff (s t : TwistedSection f L)
    (hs : SplitLineAffineNeighborhood.LocallySplit (s.toDirectImage f L).map)
    (ht : SplitLineAffineNeighborhood.LocallySplit (t.toDirectImage f L).map) :
    (DualAtlasLineQuotient.lineSetoid _).r
        (originalTwistLine f L s.baseLine s.section_ hs)
        (originalTwistLine f L t.baseLine t.section_ ht) ↔ originalTwistIsoRelation f L s t := by
  unfold originalTwistIsoRelation
  exact originalTwistLine_rel_iff_iso f L s t hs ht

/-- A twisting-line orbit supplies the full original section-preserving total-space isomorphism. -/
lemma originalTwistIsoRelation_section (s t : TwistedSection f L)
    (h : originalTwistIsoRelation f L s t) : (twistedSectionSetoid f L).r s t := by
  unfold originalTwistIsoRelation at h
  obtain ⟨e, he⟩ := h
  exact ⟨congr (Iso.refl L) ((pullback f).mapIso e), he⟩

end FLT.Mazur.CartierAbel
