/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAssociativity
public import FLT.Mazur.EllipticFormalBaseChange
public import FLT.Mazur.EllipticFormalLinearTerms
public import Mathlib.RingTheory.FormalGroup.Basic

/-!
# The integral elliptic formal group law

Associativity over the polynomial ring in the five Weierstrass coefficients
specializes to every commutative coefficient ring. Together with the previously
proved linear terms and symmetry, it constructs the commutative formal group
of the Weierstrass curve at infinity, without a discriminant assumption.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open MvPowerSeries

/-- The universal Weierstrass curve over its integral coefficient ring. -/
noncomputable def universalWeierstrass : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Specialization to the five coefficients of a given curve. -/
def coefficientSpecialization : MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/-- Every Weierstrass curve is a specialization of the universal curve. -/
@[simp] theorem universalWeierstrass_map :
    universalWeierstrass.map (coefficientSpecialization W) = W := by
  ext <;> simp [universalWeierstrass, coefficientSpecialization]

/-- Associativity at the three formal variables over every commutative ring. -/
theorem add_assoc_variables :
    add W (add W (X 0) (X 1)) (X 2) =
      add W (X 0) (add W (X 1) (X 2)) (σ := Fin 3) := by
  have h := congrArg (MvPowerSeries.map (coefficientSpecialization W))
    (add_assoc_variables_of_domain universalWeierstrass)
  simpa only [map_addition, constantCoeff_X, constantCoeff_add, map_X,
    universalWeierstrass_map] using h

/-- The actual three-variable substitution identity for the addition series. -/
theorem additionSeries_assoc :
    (additionSeries W).subst
      ![(additionSeries W).subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1], X 2] =
      (additionSeries W).subst ![X 0, (additionSeries W).subst ![X 1, X 2]]
        (τ := Fin 3) (S := R) := by
  rw [additionSeries_subst W (t := X 0) (v := X 1) (by simp) (by simp),
    additionSeries_subst W (t := X 1) (v := X 2) (by simp) (by simp),
    additionSeries_subst W (constantCoeff_add W (by simp) (by simp)) (by simp),
    additionSeries_subst W (by simp) (constantCoeff_add W (by simp) (by simp))]
  exact add_assoc_variables W

/-- The integral formal group of a Weierstrass curve at infinity. -/
noncomputable def formalGroup : FormalGroup R where
  toPowerSeries := additionSeries W
  zero_constantCoeff := constantCoeff_additionSeries W
  lin_coeff_X := additionSeries_coeff_X W
  lin_coeff_Y := additionSeries_coeff_Y W
  assoc := additionSeries_assoc W

/-- Elliptic formal addition is commutative. -/
instance formalGroup_isComm : (formalGroup W).IsComm where
  comm := (additionSeries_swap W).symm

/-- Associativity for arbitrary zero-constant formal parameters. -/
theorem add_assoc {σ : Type*} {t v w : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (hw : w.constantCoeff = 0) :
    add W (add W t v) w = add W t (add W v w) := by
  have h := (formalGroup W).assoc' (PowerSeries.HasSubst.of_constantCoeff_zero ht)
    (PowerSeries.HasSubst.of_constantCoeff_zero hv) (PowerSeries.HasSubst.of_constantCoeff_zero hw)
  change (additionSeries W).subst ![(additionSeries W).subst ![t, v], w] =
    (additionSeries W).subst ![t, (additionSeries W).subst ![v, w]] at h
  simpa only [additionSeries_subst W ht hv, additionSeries_subst W hv hw,
    additionSeries_subst W (constantCoeff_add W ht hv) hw,
    additionSeries_subst W ht (constantCoeff_add W hv hw)] using h

end FLT.Mazur.FormalInfinity
