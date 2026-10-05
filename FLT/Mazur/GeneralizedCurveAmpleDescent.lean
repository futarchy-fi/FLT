/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveAmpleBaseChange
public import FLT.Mazur.GeneralizedCurveCartierDescent
public import FLT.Mazur.RelativeAmpleFpqcDescent

/-!
# Fpqc descent of ampleness for actual subgroup divisors

The divisor-line pullback comparison transports an upstairs ample witness
to the pullback of the original line. Relative ampleness then descends.
For cyclic subgroups the required original Cartier condition is already proved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme.{0}} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) (g : T ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]

/-- Ampleness of a Cartier subgroup divisor descends along any fpqc base change. -/
theorem isAmple_of_baseChange (hI : EffectiveCartier H.ideal)
    (hH : (H.baseChange g).IsAmple) : H.IsAmple := by
  let := E.family.family.1
  obtain ⟨hJ, hL⟩ := hH
  let := H.idealPullbackHom_isIso hI g
  have he := divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g) hI hJ
    (H.baseChange_ideal g).symm
  exact ⟨hI, (hL.of_iso he).of_fpqc hI.divisorLineBundle_locallyFreeRankOne
    (IsPullback.of_hasPullback E.curve.hom g)⟩

/-- For cyclic finite subgroups, ampleness is fpqc invariant with no extra Cartier assumption. -/
theorem IsCyclic.isAmple_baseChange_iff (hH : H.IsCyclic) :
    (H.baseChange g).IsAmple ↔ H.IsAmple :=
  ⟨H.isAmple_of_baseChange g (hH.effectiveCartier H), fun hA ↦ hA.baseChange g⟩

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
