/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonSubgroupAmple

/-!
# Ampleness of subgroups on arbitrary base changes of arithmetic one-gons

Every geometric fiber of a base-changed arithmetic one-gon is integral.
Consequently every positive-rank Cartier subgroup meets its sole component
and is ample, without requiring it to descend from a subgroup before base change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonSubgroupAmple

open OneGonSmoothing ArithmeticOneGonGeneralizedCurve ArithmeticOneGonFieldFibers
open WeierstrassIntegralChart FCurve GeneralizedEllipticCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))
  {T : Scheme} (g : T ⟶ Spec (.of R)) {n : ℕ}
  (H : ((curve t ht).baseChange g).FiniteSubgroup n)

/-- Positive Cartier subgroups are ample on every base change of the genuine one-gon family. -/
theorem isAmple_after_baseChange (hn : 0 < n) (hI : EffectiveCartier H.ideal) :
    H.IsAmple := by
  let E := (curve t ht).baseChange g
  let _ : IsProper E.curve.hom := E.family.family.1
  refine ⟨hI, relativeAmple_of_ample_fibers_proper E.curve.hom _
    hI.divisorLineBundle_locallyFreeRankOne (fun s => ?_)⟩
  let f := T.fromSpecResidueField s
  let J := H.baseChange f
  let hJ := H.effectiveCartier_baseChange hI f
  let _ := H.idealPullbackHom_isIso hI f
  let _ : IsProper (E.baseChange f).curve.hom := (E.baseChange f).family.family.1
  have hp := (IsPullback.of_hasPullback E.curve.hom f).paste_horiz
    (IsPullback.of_hasPullback (curve t ht).curve.hom g)
  let _ : IsIntegral (E.baseChange f).curve.left :=
    integralCurveFieldSquare_isIntegral (equation t) (f ≫ g) _ _ hp
  let _ : IsFinite (J.ideal.subschemeι ≫ (E.baseChange f).curve.hom) := J.ideal_degree.1
  have hc := cartesian_classified t ht _ (f ≫ g) _ _ hp
  have ha : AmpleLineBundle (divisorLineBundle J.ideal hJ) := by
    apply (divisor_ample_iff_meets_components (E.baseChange f).curve.hom hJ hc.pureDimension).mpr
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst Z
    rw [Set.inter_univ]
    exact J.support_nonempty_of_positive hn
  exact ha.of_iso (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom f) hI hJ
    (H.baseChange_ideal f).symm)

end FLT.Mazur.ArithmeticOneGonSubgroupAmple
