/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonGeneralizedCurve
public import FLT.Mazur.SmoothFiniteSubgroupAmple

/-!
# Ampleness of Cartier subgroups on arithmetic one-gon degenerations

Every field fiber of the actual arithmetic cubic is integral. Positive rank
makes a finite subgroup meet that component; its Cartier divisor line is ample
on every fiber and hence relatively ample on the original arithmetic family.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonSubgroupAmple

open OneGonSmoothing ArithmeticOneGonGeneralizedCurve ArithmeticOneGonFieldFibers
open WeierstrassIntegralChart FCurve GeneralizedEllipticCurve

variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))
  {n : ℕ} (H : (curve t ht).FiniteSubgroup n)

/-- Every positive finite Cartier subgroup on the arithmetic degeneration is relatively ample. -/
theorem isAmple (hn : 0 < n) (hI : EffectiveCartier H.ideal) : H.IsAmple := by
  let E := curve t ht
  let _ : IsProper E.curve.hom := E.family.family.1
  refine ⟨hI, relativeAmple_of_ample_fibers_proper E.curve.hom _
    hI.divisorLineBundle_locallyFreeRankOne (fun s ↦ ?_)⟩
  let g := (Spec (.of R)).fromSpecResidueField s
  let J := H.baseChange g
  let hJ := H.effectiveCartier_baseChange hI g
  let _ := H.idealPullbackHom_isIso hI g
  let _ : IsProper (E.baseChange g).curve.hom := (E.baseChange g).family.family.1
  let _ : IsIntegral (E.baseChange g).curve.left :=
    integralCurveFieldSquare_isIntegral (equation t) g _ _ (IsPullback.of_hasPullback _ _)
  let _ : IsFinite (J.ideal.subschemeι ≫ (E.baseChange g).curve.hom) := J.ideal_degree.1
  have hc := cartesian_classified t ht _ g _ _
    (IsPullback.of_hasPullback E.curve.hom g)
  have ha : AmpleLineBundle (divisorLineBundle J.ideal hJ) := by
    apply (divisor_ample_iff_meets_components (E.baseChange g).curve.hom hJ hc.pureDimension).mpr
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst Z
    rw [Set.inter_univ]
    exact J.support_nonempty_of_positive hn
  exact ha.of_iso (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g) hI hJ
    (H.baseChange_ideal g).symm)

end FLT.Mazur.ArithmeticOneGonSubgroupAmple
