/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.IdealAdicLineQuotient
public import FLT.Mazur.IsomorphicClosedPullback
public import FLT.Mazur.PolygonArithmeticAdicImmersion

/-!
# Line quotients along the original polygon stage transition

The parameter-adic quotient of a line sheaf on an upper stage is the direct
image of its actual pullback to the next lower stage. Its projection is the
original pullback unit, rather than an unspecified isomorphism of quotients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve IdealAdicQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (m n : ℕ) (h : 2 ≤ n)
  (L : (family A π (m + 1) n h).left.Modules) (hL : LocallyFreeRankOne L)

/-- The ideal-adic line quotient is the original lower-stage pullback, pushed forward. -/
def stageLineQuotientIso : quotient (stageParameterIdeal A π (m + 1) n h) L (m + 1) ≅
    (pushforward (stageRestriction A π m n h)).obj
      ((pullback (stageRestriction A π m n h)).obj L) :=
  lineQuotientClosedIso _ L hL (m + 1) ≪≫
    IsomorphicClosedPullback.overIso (stageRestrictionIdealIso A π m n h)
      (stageParameterIdeal A π (m + 1) n h ^ (m + 1)).subschemeι L
      (stageRestriction A π m n h) (stageRestrictionIdealIso_hom_ι A π m n h)

/-- The comparison carries the quotient projection to the original restriction unit. -/
@[reassoc] theorem projection_stageLineQuotientIso :
    projection (stageParameterIdeal A π (m + 1) n h) L (m + 1) ≫
      (stageLineQuotientIso A π m n h L hL).hom =
        (pullbackPushforwardAdjunction (stageRestriction A π m n h)).unit.app L := by
  rw [stageLineQuotientIso, Iso.trans_hom, ← Category.assoc,
    projection_lineQuotientClosedIso, IsomorphicClosedPullback.unit_overIso]

end FLT.Mazur.PolygonArithmeticStages
