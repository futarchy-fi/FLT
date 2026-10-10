/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankOneAmbientLineClassification
public import FLT.Mazur.OriginalTwistOrbitRelation

/-!
# Full zero ideals of sections with rank-one direct image

The unique comparison between the original dual twisting lines induces an
isomorphism of the original tensor sections. Hence the full zero ideals
agree, without discarding nilpotents or multiplicities.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient SplitLineAffineNeighborhood
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  (hN : LocallyFreeRankOne ((pushforward f).obj L))
  (s t : TwistedSection f L)
  (hs : LocallySplit (s.toDirectImage f L).map)
  (ht : LocallySplit (t.toDirectImage f L).map)

include hN hs ht in
/-- Invertible original inclusions identify the original twisting lines and sections. -/
theorem rankOne_originalTwistIsoRelation : originalTwistIsoRelation f L s t := by
  apply (originalTwistLine_rel_iff f L s t hs ht).mp
  exact lineSetoid_rankOne hN _ _

include hN hs ht in
/-- The comparison preserves actual total-space sections, before taking zero ideals. -/
theorem rankOne_twistedSection_relation : (twistedSectionSetoid f L).r s t :=
  originalTwistIsoRelation_section f L s t
    (rankOne_originalTwistIsoRelation f L hN s t hs ht)

include hN hs ht in
/-- The original sections define the same full Cartier Abel fiber element. -/
theorem rankOne_twistedSection_fiber_eq (hL : LocallyFreeRankOne L) :
    s.toFiber f L hL = t.toFiber f L hL :=
  (twistedSection_toFiber_eq_iff f L hL s t).mpr
    (rankOne_twistedSection_relation f L hN s t hs ht)

include hN hs ht in
/-- Equality is of the full zero ideal sheaves, including their nonreduced structures. -/
theorem rankOne_twistedSection_zeroIdeal_eq (hL : LocallyFreeRankOne L) :
    lineSectionZeroIdeal (twist_rankOne f L hL s.baseLine) s.section_ =
      lineSectionZeroIdeal (twist_rankOne f L hL t.baseLine) t.section_ :=
  congrArg (fun D : Fiber f L hL ↦ D.val.val)
    (rankOne_twistedSection_fiber_eq f L hN s t hs ht hL)

end FLT.Mazur.CartierAbel
