/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicLineQuotient
public import FLT.Mazur.IsomorphicClosedPullback

/-!
# Line quotients with a specified presentation of the closed source

The quotient comparison and its unit identity are constructed before
specializing to a concrete geometric source, keeping the transport proof small.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.ClosedLineQuotientPresentation

open FCurve IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme} (I : X.IdealSheafData) (L : X.Modules)
  (hL : LocallyFreeRankOne L) (n : ℕ) (e : Y ≅ (I ^ n).subscheme)
  (f : Y ⟶ X) (hf : e.hom ≫ (I ^ n).subschemeι = f)

/-- A specified presentation of the closed subscheme gives the actual line quotient. -/
@[irreducible] def quotientIso : quotient I L n ≅
    (pushforward f).obj ((pullback f).obj L) :=
  lineQuotientClosedIso I L hL n ≪≫
    IsomorphicClosedPullback.overIso e (I ^ n).subschemeι L f hf

/-- This comparison retains the original pullback unit of the specified inclusion. -/
@[reassoc] theorem projection_quotientIso :
    projection I L n ≫ (quotientIso I L hL n e f hf).hom =
      (pullbackPushforwardAdjunction f).unit.app L := by
  rw [quotientIso, Iso.trans_hom, ← Category.assoc,
    projection_lineQuotientClosedIso, IsomorphicClosedPullback.unit_overIso]

end FLT.Mazur.ClosedLineQuotientPresentation
