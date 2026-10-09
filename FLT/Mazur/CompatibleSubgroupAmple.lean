/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso
public import FLT.Mazur.GeneralizedCurveAmpleBaseChange

/-!
# Ampleness under compatible subgroup isomorphisms

The compatible inclusion square identifies the actual subgroup ideals. Pullback
along the inverse curve isomorphism transports the Cartier condition and the
positive divisor line bundle, preserving relative ampleness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

open FCurve

variable {S : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Compatible isomorphisms preserve ampleness of the actual subgroup divisor. -/
theorem CompatibleIso.isAmple (a : CompatibleIso H J) (hH : H.IsAmple) : J.IsAmple := by
  obtain ⟨hI, hL⟩ := hH
  have : IsIso a.curve.inv.curve.left :=
    inferInstanceAs (IsIso ((forgetCurve ⋙ Over.forget S).map a.curve.inv))
  have hi := ideal_transport H J a.curve a.subgroup a.compatible
  have hJ : EffectiveCartier J.ideal := by
    rw [hi]
    exact hI.comap_of_isOpenImmersion a.curve.inv.curve.left
  have sq : IsPullback a.curve.inv.curve.left F.curve.hom E.curve.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨hJ, (hL.of_isPullback hI.divisorLineBundle_locallyFreeRankOne sq).of_iso
    (divisorLinePullbackIsoOfEq a.curve.inv.curve.left hI hJ hi.symm).symm⟩

/-- Relative ampleness is invariant under compatible isomorphism. -/
theorem CompatibleIso.isAmple_iff (a : CompatibleIso H J) : H.IsAmple ↔ J.IsAmple :=
  ⟨a.isAmple, a.symm.isAmple⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
