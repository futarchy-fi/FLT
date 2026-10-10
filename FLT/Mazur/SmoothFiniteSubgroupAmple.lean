/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveDivisorPullback
public import FLT.Mazur.GeneralizedCurveFiberAmple
public import FLT.Mazur.ProperOnlyRelativeAmpleFibers

/-!
# Positive finite Cartier subgroups on smooth integral families are ample

Positive rank makes every residue-field subgroup divisor nonempty. The proved
curve criterion gives ampleness on each fiber, and the proper fiber criterion
then gives relative ampleness on the whole base, including nonaffine bases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

open FCurve

variable {S : Scheme.{0}} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n)

/-- Positive rank gives a nonempty subgroup divisor over any nonempty base. -/
theorem support_nonempty_of_positive [Nonempty S] (hn : 0 < n) :
    (H.ideal.support : Set E.curve.left).Nonempty := by
  let _ := H.surjective hn
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨x, _⟩ := H.carrier.hom.surjective s
  rw [ideal, Scheme.Hom.support_ker]
  exact ⟨_, subset_closure ⟨x, rfl⟩⟩

/-- Every positive Cartier subgroup on a smooth geometrically integral family is ample. -/
theorem isAmple_of_smooth [SmoothOfRelativeDimension 1 E.curve.hom]
    [GeometricallyIntegral E.curve.hom] (hn : 0 < n) (hI : EffectiveCartier H.ideal) :
    H.IsAmple := by
  have : IsProper E.curve.hom := E.family.family.1
  refine ⟨hI, relativeAmple_of_ample_fibers_proper E.curve.hom _
    hI.divisorLineBundle_locallyFreeRankOne (fun s ↦ ?_)⟩
  let g := S.fromSpecResidueField s
  let J := H.baseChange g
  let hJ := H.effectiveCartier_baseChange hI g
  let _ := H.idealPullbackHom_isIso hI g
  have : IsProper (E.baseChange g).curve.hom := (E.baseChange g).family.family.1
  have : SmoothOfRelativeDimension 1 (E.baseChange g).curve.hom :=
    MorphismProperty.pullback_snd E.curve.hom g inferInstance
  have : GeometricallyIntegral (E.baseChange g).curve.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd E.curve.hom g))
  have : IsIntegral (E.baseChange g).curve.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (E.baseChange g).curve.hom
  have : IsFinite (J.ideal.subschemeι ≫ (E.baseChange g).curve.hom) := J.ideal_degree.1
  have ha : AmpleLineBundle (divisorLineBundle J.ideal hJ) :=
    (divisor_ample_iff_nonempty (E.baseChange g).curve.hom hJ
      (smoothCurveDimension (E.baseChange g).curve.hom inferInstance inferInstance)).mpr
        (J.support_nonempty_of_positive hn)
  exact ha.of_iso (divisorLinePullbackIsoOfEq (pullback.fst E.curve.hom g) hI hJ
    (H.baseChange_ideal g).symm)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
