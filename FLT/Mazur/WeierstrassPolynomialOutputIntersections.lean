/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPolynomialOutputComparison
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Actual intersections of polynomial addition output opens

Localizing one output domain at another output coordinate constructs their
scheme intersection. Its two addition maps factor through the output-chart
transition, including when their selected output coordinates differ.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k t u : Fin 3)

/-- Two polynomial laws with the same inputs have proportional normalized outputs. -/
theorem polynomialOutput_scaled
    (f : AdditionOutputOpen W j k t →ₐ[R] S)
    (g : AdditionOutputOpen W j k u →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W j k t) =
      g.comp (additionOutputRestriction W j k u)) (i : Fin 3) :
    g (additionOutputRestriction W j k u (chartProductAdditionCoordinates W j k i)) =
      f (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t)) *
        (f.comp (projectiveAdditionChart W j k t)) (coord W t i) := by
  have hi := congrArg f (projectiveAdditionChart_mul W j k t i)
  rw [map_mul] at hi
  exact (DFunLike.congr_fun h _).symm.trans (hi.symm.trans (mul_comm _ _))

/-- The common restriction of two polynomial laws maps to the actual output overlap. -/
def polynomialOutputLift
    (f : AdditionOutputOpen W j k t →ₐ[R] S)
    (g : AdditionOutputOpen W j k u →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W j k t) =
      g.comp (additionOutputRestriction W j k u)) : Overlap W u t →ₐ[R] S :=
  polynomialComparisonLift W j k u t g (f.comp (projectiveAdditionChart W j k t))
    (f (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t)))
    (polynomialOutput_scaled W j k t u f g h)

/-- The output-overlap map retains the second polynomial law. -/
theorem polynomialOutputLift_restriction
    (f : AdditionOutputOpen W j k t →ₐ[R] S)
    (g : AdditionOutputOpen W j k u →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W j k t) =
      g.comp (additionOutputRestriction W j k u)) :
    (polynomialOutputLift W j k t u f g h).comp (overlapRestriction W u t) =
      g.comp (projectiveAdditionChart W j k u) :=
  polynomialComparisonLift_restriction ..

/-- Changing output charts recovers the first polynomial law. -/
theorem polynomialOutputLift_transition
    (f : AdditionOutputOpen W j k t →ₐ[R] S)
    (g : AdditionOutputOpen W j k u →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W j k t) =
      g.comp (additionOutputRestriction W j k u)) :
    (polynomialOutputLift W j k t u f g h).comp (transitionBase W u t) =
      f.comp (projectiveAdditionChart W j k t) :=
  polynomialComparisonLift_transition ..

/-- The concrete intersection of two polynomial output domains. -/
abbrev PolynomialOutputIntersection := Localization.Away
  (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k u))

/-- The first polynomial domain restricts to the intersection. -/
def polynomialOutputFirst : AdditionOutputOpen W j k t →ₐ[R]
    PolynomialOutputIntersection W j k t u :=
  IsScalarTower.toAlgHom R _ _

/-- The other polynomial coordinate becomes invertible on the intersection. -/
theorem polynomialOutputSecond_isUnit : IsUnit
    ((polynomialOutputFirst W j k t u).comp (additionOutputRestriction W j k t)
      (chartProductAdditionCoordinates W j k u)) :=
  IsLocalization.Away.algebraMap_isUnit
    (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k u))

/-- The second polynomial domain restricts to the same intersection. -/
def polynomialOutputSecond : AdditionOutputOpen W j k u →ₐ[R]
    PolynomialOutputIntersection W j k t u :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j k u)
    (polynomialOutputSecond_isUnit W j k t u)

/-- The two restrictions have identical input coordinates. -/
theorem polynomialOutputIntersection_inputs :
    (polynomialOutputSecond W j k t u).comp (additionOutputRestriction W j k u) =
      (polynomialOutputFirst W j k t u).comp (additionOutputRestriction W j k t) := by
  apply AlgHom.coe_ringHom_injective
  exact IsLocalization.Away.lift_comp (chartProductAdditionCoordinates W j k u)
    (S := AdditionOutputOpen W j k u)
    (g := ((polynomialOutputFirst W j k t u).comp
      (additionOutputRestriction W j k t)).toRingHom)
    (polynomialOutputSecond_isUnit W j k t u)

/-- Output compatibility on the concrete intersection, with no common-map assumption. -/
def polynomialOutputIntersectionLift :
    Overlap W u t →ₐ[R] PolynomialOutputIntersection W j k t u :=
  polynomialOutputLift W j k t u (polynomialOutputFirst W j k t u)
    (polynomialOutputSecond W j k t u) (polynomialOutputIntersection_inputs W j k t u).symm

/-- The concrete comparison restricts to the second output. -/
theorem polynomialOutputIntersectionLift_restriction :
    (polynomialOutputIntersectionLift W j k t u).comp (overlapRestriction W u t) =
      (polynomialOutputSecond W j k t u).comp (projectiveAdditionChart W j k u) :=
  polynomialOutputLift_restriction ..

/-- The concrete comparison changes charts to the first output. -/
theorem polynomialOutputIntersectionLift_transition :
    (polynomialOutputIntersectionLift W j k t u).comp (transitionBase W u t) =
      (polynomialOutputFirst W j k t u).comp (projectiveAdditionChart W j k t) :=
  polynomialOutputLift_transition ..

open AlgebraicGeometry CategoryTheory

/-- The constructed intersection is the actual scheme fiber product of the output opens. -/
theorem polynomialOutputIntersection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (polynomialOutputFirst W j k t u).toRingHom))
      (Spec.map (CommRingCat.ofHom (polynomialOutputSecond W j k t u).toRingHom))
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom))
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k u).toRingHom)) := by
  have : IsLocalization
      ((Submonoid.powers (chartProductAdditionCoordinates W j k u)).map
        (additionOutputRestriction W j k t).toRingHom)
      (PolynomialOutputIntersection W j k t u) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization
    (additionOutputRestriction W j k t).toRingHom
    (polynomialOutputSecond W j k t u).toRingHom
    (congrArg AlgHom.toRingHom (polynomialOutputIntersection_inputs W j k t u))
    (Submonoid.powers (chartProductAdditionCoordinates W j k u))

end FLT.Mazur.WeierstrassIntegralChart
