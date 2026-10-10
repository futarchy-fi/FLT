/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionBidual
public import FLT.Mazur.RetainedLineTwistedSection

/-!
# Retaining an independently specified original twist

Canonical biduality identifies the original tensor section with the intrinsic
section of its retained direct-image line, preserving its full zero ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve DualAtlasLineQuotient ModuleSheafTensor SplitLineAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
  lineSheafBidualIso moduleSheafDualMap
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  (B : SchemePicard.LineBundle S) (s : Γ(tensor L ((pullback f).obj B.val), ⊤))
  (hs : LocallySplit (twistedSectionPushforwardEquiv f L B.property s))

/-- The original twisting line and section supply their own retained direct-image line. -/
abbrev originalTwistLine : Line ((pushforward f).obj L) :=
  ⟨moduleSheafDual B.val, B.property.dual,
    twistedSectionPushforwardEquiv f L B.property s, hs⟩

/-- The original twisting line identifies with the intrinsic retained twist by biduality. -/
@[irreducible] def originalTwistIso :
    B.val ≅ moduleSheafDual (originalTwistLine f L B s hs).source :=
  lineSheafBidualIso B.property

/-- The dual of the original twisting comparison is inverse biduality of its retained source. -/
lemma originalTwistIso_dual :
    moduleSheafDualMap B.val (originalTwistIso f L B s hs).hom =
      (lineSheafBidualIso (originalTwistLine f L B s hs).rankOne).inv := by
  unfold originalTwistIso
  exact (lineSheafBidual_dual_inv B.property).symm

/-- The intrinsic retained section remembers the independently specified original twist. -/
lemma originalTwistLine_section :
    (map (𝟙 L) ((pullback f).map (originalTwistIso f L B s hs).hom)).app ⊤ s =
      retainedLineSection f L (originalTwistLine f L B s hs) := by
  apply (twistedSectionPushforwardEquiv f L
    (originalTwistLine f L B s hs).rankOne.dual).injective
  rw [twistedSectionPushforwardEquiv_baseLineIso f L (originalTwistIso f L B s hs)
    B.property (originalTwistLine f L B s hs).rankOne.dual,
    retainedLineSection_map, originalTwistIso_dual]

end FLT.Mazur.CartierAbel
