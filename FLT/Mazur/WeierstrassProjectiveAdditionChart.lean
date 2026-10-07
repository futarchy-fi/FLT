/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicPolarization
public import FLT.Mazur.WeierstrassProjectiveAdditionBoundary

/-!
# Regular projective addition on an output-coordinate open

The polynomial addition law satisfies the cubic on every integral input-chart
product. Inverting any selected output coordinate therefore gives an actual
algebra map from that normalized Weierstrass chart.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k t : Fin 3)

/-- The addition polynomials solve the cubic after every specialization of the product. -/
theorem chartProductAdditionCoordinates_equation (f : ChartProduct W j k →ₐ[R] S) :
    (W.map (algebraMap R S)).toProjective.Equation
      (f ∘ chartProductAdditionCoordinates W j k) := by
  rw [chartProductAdditionCoordinates_map]
  exact projectiveAdd_equation _ (chartProductLeft_equation W j k f)
    (chartProductRight_equation W j k f)

/-- The principal open where output coordinate t of the polynomial law is invertible. -/
abbrev AdditionOutputOpen := Localization.Away (chartProductAdditionCoordinates W j k t)

/-- Restriction of the input product to the selected output open. -/
def additionOutputRestriction : ChartProduct W j k →ₐ[R] AdditionOutputOpen W j k t :=
  IsScalarTower.toAlgHom R (ChartProduct W j k) (AdditionOutputOpen W j k t)

/-- The selected homogeneous coordinate becomes a unit on its principal open. -/
theorem additionOutput_isUnit :
    IsUnit (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t)) :=
  IsLocalization.Away.algebraMap_isUnit (chartProductAdditionCoordinates W j k t)

/-- The inverse coordinate used to normalize the polynomial addition law. -/
def additionOutputInverse : AdditionOutputOpen W j k t :=
  ↑(additionOutput_isUnit W j k t).unit⁻¹

/-- The normalizing factor cancels the chosen output coordinate. -/
@[simp] theorem additionOutputInverse_mul :
    additionOutputInverse W j k t *
      additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t) = 1 :=
  Units.inv_mul_eq_one.mpr (additionOutput_isUnit W j k t).unit_spec

/-- The normalized polynomial law defines a regular map into the chosen curve chart. -/
def projectiveAdditionChart : Coordinate W t →ₐ[R] AdditionOutputOpen W j k t :=
  evaluation W t
    (additionOutputInverse W j k t •
      (additionOutputRestriction W j k t ∘ chartProductAdditionCoordinates W j k))
    (((W.map (algebraMap R (AdditionOutputOpen W j k t))).toProjective.equation_smul _
      (Units.isUnit _)).mpr
        (chartProductAdditionCoordinates_equation W j k (additionOutputRestriction W j k t)))
    (additionOutputInverse_mul W j k t)

/-- The chart morphism has precisely the normalized polynomial coordinates. -/
@[simp] theorem projectiveAdditionChart_coord (i : Fin 3) :
    projectiveAdditionChart W j k t (coord W t i) = additionOutputInverse W j k t *
      additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k i) :=
  evaluation_coord W t _ _ _ i

/-- Clearing the normalizing coordinate recovers the original homogeneous output. -/
theorem projectiveAdditionChart_mul (i : Fin 3) :
    projectiveAdditionChart W j k t (coord W t i) *
      additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t) =
      additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k i) := by
  rw [projectiveAdditionChart_coord]
  linear_combination
    additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k i) *
      additionOutputInverse_mul W j k t

/-- After any restriction, clearing the denominator characterizes this chart map uniquely. -/
theorem projectiveAdditionChart_comp_eq (f : AdditionOutputOpen W j k t →ₐ[R] S)
    (g : Coordinate W t →ₐ[R] S)
    (h : ∀ i, g (coord W t i) *
      f (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k t)) =
      f (additionOutputRestriction W j k t (chartProductAdditionCoordinates W j k i))) :
    f.comp (projectiveAdditionChart W j k t) = g := by
  apply hom_ext
  intro i
  apply ((additionOutput_isUnit W j k t).map f).mul_left_inj.mp
  have hi := congrArg f (projectiveAdditionChart_mul W j k t i)
  simp only [map_mul] at hi
  exact hi.trans (h i).symm

end FLT.Mazur.WeierstrassIntegralChart
