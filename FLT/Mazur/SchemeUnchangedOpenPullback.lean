/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeUnchangedOpenLift

/-!
# Transport unchanged opens through a full chart pullback

A complete target-chart pullback lets an unchanged open of the chart be
recognized as an unchanged open of the whole target scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeUnchangedOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T A : Scheme} (f : X ⟶ Y) (g : A ⟶ T)
  (i : T ⟶ Y) [IsOpenImmersion i] (j : A ⟶ X)

/-- A full chart pullback transports its unchanged opens to the whole target. -/
theorem isIso_of_chart_pullback (H : IsPullback g j i f) (U : T.Opens)
    (hU : IsIso (g ∣_ U)) : IsIso (f ∣_ (U.ι ≫ i).opensRange) := by
  have h : IsIso (g ∣_ U.ι.opensRange) := by
    rw [U.opensRange_ι]
    exact hU
  exact isIso_of_identity_pullback f (U.ι ≫ i) (lift g U.ι h ≫ j)
    ((lift_isPullback g U.ι h).paste_vert H)

end FLT.Mazur.SchemeUnchangedOpen
