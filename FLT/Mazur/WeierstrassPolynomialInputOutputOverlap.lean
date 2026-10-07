/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassPolynomialInputTransition
public import FLT.Mazur.WeierstrassPolynomialOutputComparison

/-!
# Polynomial addition with both input and output chart changes

On the simultaneous input overlap, invert the two selected output coordinates.
The original and changed polynomial domains both restrict to this concrete
ring, and their addition maps factor through the integral output overlap.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k j' k' t u : Fin 3)

/-- The simultaneous input overlap with both polynomial output coordinates inverted. -/
abbrev InputOutputPolynomialOpen := Localization.Away
  (inputPolynomialRestriction W j k j' k' t
    (productOverlapOther W j k j' k' (chartProductAdditionCoordinates W j' k' u)))

/-- Restrict the first polynomial input overlap at the second output coordinate. -/
def inputOutputPolynomialRestriction : InputPolynomialOpen W j k j' k' t →ₐ[R]
    InputOutputPolynomialOpen W j k j' k' t u := IsScalarTower.toAlgHom R _ _

/-- The first polynomial addition domain restricts to the concrete common open. -/
def inputOutputPolynomialFirst : AdditionOutputOpen W j k t →ₐ[R]
    InputOutputPolynomialOpen W j k j' k' t u :=
  (inputOutputPolynomialRestriction W j k j' k' t u).comp
    (inputPolynomialOriginal W j k j' k' t)

/-- The underlying input overlap restricts to the same common open. -/
def inputOutputPolynomialBase : ProductOverlap W j k j' k' →ₐ[R]
    InputOutputPolynomialOpen W j k j' k' t u :=
  (inputOutputPolynomialRestriction W j k j' k' t u).comp
    (inputPolynomialRestriction W j k j' k' t)

/-- The second output coordinate is a unit in the changed input presentation. -/
theorem inputOutputPolynomial_isUnit : IsUnit
    ((inputOutputPolynomialBase W j k j' k' t u).comp (productOverlapOther W j k j' k')
      (chartProductAdditionCoordinates W j' k' u)) :=
  IsLocalization.Away.algebraMap_isUnit
    (inputPolynomialRestriction W j k j' k' t
      (productOverlapOther W j k j' k' (chartProductAdditionCoordinates W j' k' u)))

/-- The changed polynomial addition domain also restricts to the concrete common open. -/
def inputOutputPolynomialSecond : AdditionOutputOpen W j' k' u →ₐ[R]
    InputOutputPolynomialOpen W j k j' k' t u :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j' k' u)
    (inputOutputPolynomial_isUnit W j k j' k' t u)

/-- The first domain retains the original input functions on the common open. -/
theorem inputOutputPolynomialFirst_inputs (a : ChartProduct W j k) :
    inputOutputPolynomialFirst W j k j' k' t u (additionOutputRestriction W j k t a) =
      inputOutputPolynomialBase W j k j' k' t u (productOverlapRestriction W j k j' k' a) := by
  change inputOutputPolynomialRestriction W j k j' k' t u
    (inputPolynomialOriginal W j k j' k' t (additionOutputRestriction W j k t a)) = _
  rw [inputPolynomialOriginal_restriction]
  rfl

/-- The second domain retains the normalized input functions on the same common open. -/
theorem inputOutputPolynomialSecond_inputs (a : ChartProduct W j' k') :
    inputOutputPolynomialSecond W j k j' k' t u (additionOutputRestriction W j' k' u a) =
      inputOutputPolynomialBase W j k j' k' t u (productOverlapOther W j k j' k' a) :=
  IsLocalization.Away.lift_eq _ (inputOutputPolynomial_isUnit W j k j' k' t u) a

/-- The homogeneous factor incorporates both input normalization and the first output scale. -/
def inputOutputPolynomialFactor : InputOutputPolynomialOpen W j k j' k' t u :=
  inputOutputPolynomialBase W j k j' k' t u (productOverlapAdditionScale W j k j' k') *
    inputOutputPolynomialFirst W j k j' k' t u
      (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t))

/-- The two selected outputs have proportional coordinates after both input changes. -/
theorem inputOutputPolynomial_scaled (a : Fin 3) :
    inputOutputPolynomialSecond W j k j' k' t u
        (additionOutputRestriction W j' k' u (chartProductAdditionCoordinates W j' k' a)) =
      inputOutputPolynomialFactor W j k j' k' t u *
        ((inputOutputPolynomialFirst W j k j' k' t u).comp (projectiveAdditionChart W j k t))
          (coord W t a) := by
  have hs := congrArg (inputOutputPolynomialBase W j k j' k' t u)
    (productOverlap_addition_scaled W j k j' k' a)
  rw [map_mul] at hs
  have hh := (inputOutputPolynomialSecond_inputs W j k j' k' t u
    (chartProductAdditionCoordinates W j' k' a)).trans hs
  have ho := inputOutputPolynomialFirst_inputs W j k j' k' t u
    (chartProductAdditionCoordinates W j k a)
  have hi := congrArg (inputOutputPolynomialFirst W j k j' k' t u)
    (projectiveAdditionChart_mul W j k t a)
  rw [map_mul] at hi
  dsimp only [inputOutputPolynomialFactor, AlgHom.comp_apply]
  linear_combination hh - inputOutputPolynomialBase W j k j' k' t u
    (productOverlapAdditionScale W j k j' k') * ho -
    inputOutputPolynomialBase W j k j' k' t u (productOverlapAdditionScale W j k j' k') * hi

/-- Output overlap for arbitrary simultaneous input and output chart changes. -/
def inputOutputPolynomialLift : Overlap W u t →ₐ[R] InputOutputPolynomialOpen W j k j' k' t u :=
  polynomialComparisonLift W j' k' u t (inputOutputPolynomialSecond W j k j' k' t u)
    ((inputOutputPolynomialFirst W j k j' k' t u).comp (projectiveAdditionChart W j k t))
    (inputOutputPolynomialFactor W j k j' k' t u) (inputOutputPolynomial_scaled W j k j' k' t u)

/-- Restriction of the overlap-valued map gives the changed-input polynomial law. -/
theorem inputOutputPolynomialLift_restriction :
    (inputOutputPolynomialLift W j k j' k' t u).comp (overlapRestriction W u t) =
      (inputOutputPolynomialSecond W j k j' k' t u).comp (projectiveAdditionChart W j' k' u) :=
  polynomialComparisonLift_restriction ..

/-- Changing output charts gives the original-input polynomial law. -/
theorem inputOutputPolynomialLift_transition :
    (inputOutputPolynomialLift W j k j' k' t u).comp (transitionBase W u t) =
      (inputOutputPolynomialFirst W j k j' k' t u).comp (projectiveAdditionChart W j k t) :=
  polynomialComparisonLift_transition ..

open AlgebraicGeometry CategoryTheory

/-- The second localization is the pullback of the changed polynomial output domain. -/
theorem inputOutputPolynomial_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (inputOutputPolynomialRestriction W j k j' k' t u).toRingHom))
      (Spec.map (CommRingCat.ofHom (inputOutputPolynomialSecond W j k j' k' t u).toRingHom))
      (Spec.map (CommRingCat.ofHom ((inputPolynomialRestriction W j k j' k' t).comp
        (productOverlapOther W j k j' k')).toRingHom))
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j' k' u).toRingHom)) := by
  have : IsLocalization
      ((Submonoid.powers (chartProductAdditionCoordinates W j' k' u)).map
        ((inputPolynomialRestriction W j k j' k' t).comp
          (productOverlapOther W j k j' k')).toRingHom)
      (InputOutputPolynomialOpen W j k j' k' t u) := by
    rw [Submonoid.map_powers]
    change IsLocalization.Away
      (inputPolynomialRestriction W j k j' k' t
        (productOverlapOther W j k j' k' (chartProductAdditionCoordinates W j' k' u))) _
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization
    ((inputPolynomialRestriction W j k j' k' t).comp
      (productOverlapOther W j k j' k')).toRingHom
    (inputOutputPolynomialSecond W j k j' k' t u).toRingHom
    (RingHom.ext (inputOutputPolynomialSecond_inputs W j k j' k' t u))
    (Submonoid.powers (chartProductAdditionCoordinates W j' k' u))

end FLT.Mazur.WeierstrassIntegralChart
