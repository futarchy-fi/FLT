/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Etale.Kaehler
/-!
# The invariant derivation on a Weierstrass curve

The vector field `W_Y ∂/∂X - W_X ∂/∂Y` annihilates the Weierstrass equation.
It therefore descends to the coordinate ring, and extends to its fraction field
using the localization isomorphism for Kähler differentials.
-/

@[expose] public section

open Polynomial
open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (E : Affine R)
/-- The invariant vector field on bivariate polynomials. -/
noncomputable def polyDeriv : Derivation R R[X][X] R[X][X] :=
  E.polynomialY • PolynomialModule.equivPolynomialSelf.compDer
    (Polynomial.derivative' (R := R)).mapCoeffs -
  E.polynomialX • (Polynomial.derivative' (R := R[X])).restrictScalars R
/-- On polynomials in `X`, the vector field is `W_Y` times the derivative. -/
lemma polyDeriv_C (p : R[X]) : E.polyDeriv (C p) = E.polynomialY * C p.derivative := by
  simp [polyDeriv, PolynomialModule.equivPolynomialSelf]
/-- The vector field sends the outer variable `Y` to `-W_X`. -/
lemma polyDeriv_X : E.polyDeriv (X : R[X][X]) = -E.polynomialX := by
  simp [polyDeriv, PolynomialModule.equivPolynomialSelf]
/-- The invariant vector field annihilates the defining equation. -/
lemma polyDeriv_polynomial : E.polyDeriv E.polynomial = 0 := by
  simp only [polynomial, map_sub, map_add, (E.polyDeriv).leibniz,
    (E.polyDeriv).leibniz_pow, E.polyDeriv_C, E.polyDeriv_X, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, show 2-1=1 by decide, pow_one,
    derivative_C, derivative_mul, derivative_pow,
    derivative_X, map_zero, mul_zero, zero_mul, zero_add, add_zero]
  simp only [polynomialX, polynomialY, map_add, map_mul, map_pow, map_ofNat, map_one]
  ring
/-- The invariant derivation on the coordinate ring. -/
noncomputable def coordDeriv : Derivation R E.CoordinateRing E.CoordinateRing :=
  (E.polyDeriv).liftOfSurjective
    (f := (AdjoinRoot.mkₐ E.polynomial).restrictScalars R) AdjoinRoot.mk_surjective (by
      intro p hp
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_eq_zero.mp hp
      simp [Derivation.leibniz, smul_eq_mul, E.polyDeriv_polynomial])
/-- The coordinate-ring derivation agrees with the polynomial vector field. -/
lemma coordDeriv_mk (p : R[X][X]) :
    E.coordDeriv (AdjoinRoot.mk E.polynomial p) =
      AdjoinRoot.mk E.polynomial (E.polyDeriv p) := by
  unfold coordDeriv
  apply Derivation.liftOfSurjective_apply
/-- The invariant derivation extended to the fraction field of the coordinate ring. -/
noncomputable def fractionDeriv :
    Derivation R (FractionRing E.CoordinateRing) (FractionRing E.CoordinateRing) := by
  let S := E.CoordinateRing
  let F := FractionRing S
  letI : Algebra.FormallyEtale S F := Algebra.FormallyEtale.of_isLocalization S⁰
  let d : Derivation R S F := (Algebra.linearMap S F).compDer E.coordDeriv
  exact ((d.liftKaehlerDifferential.liftBaseChange F).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S F).symm.toLinearMap).compDer
      (KaehlerDifferential.D R F)
/-- Extending the invariant derivation preserves its values on the coordinate ring. -/
lemma fractionDeriv_algebraMap (p : E.CoordinateRing) :
    E.fractionDeriv (algebraMap E.CoordinateRing (FractionRing E.CoordinateRing) p) =
      algebraMap E.CoordinateRing (FractionRing E.CoordinateRing) (E.coordDeriv p) := by
  simp [fractionDeriv, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
end WeierstrassCurve.Affine


