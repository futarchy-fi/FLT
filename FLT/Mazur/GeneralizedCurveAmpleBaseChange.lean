/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveDivisorPullback
public import FLT.Mazur.RelativeAmpleBaseChange
public import FLT.Mazur.RelativeAmplePresentationTransport

/-!
# Arbitrary base change of ample finite subgroups

The subgroup's actual Cartier ideal and positive divisor line bundle commute
with base change. General relative ampleness transport therefore gives the
ample subgroup predicate over every new base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open FCurve
variable {S T : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  {H : E.FiniteSubgroup n}

/-- An ample finite subgroup remains ample after every scheme base change. -/
theorem IsAmple.baseChange (hH : H.IsAmple) (g : T ⟶ S) : (H.baseChange g).IsAmple := by
  obtain ⟨hI, hL⟩ := hH
  let hJ := H.effectiveCartier_baseChange hI g
  let := H.idealPullbackHom_isIso hI g
  refine ⟨hJ, ?_⟩
  exact (hL.baseChange hI.divisorLineBundle_locallyFreeRankOne g).of_iso
    (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g) hI hJ
      (H.baseChange_ideal g).symm).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
