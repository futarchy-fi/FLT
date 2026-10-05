/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalCoordinates
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Formal infinity coordinates as projective points

The partial derivative with respect to Z is a unit at every zero-constant formal
parameter. The normalized representative [t : -1 : s(t)] therefore defines a
nonsingular point, and its projective class determines t uniquely. The unit
statement holds over arbitrary coefficient rings, without a discriminant condition.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The normalized representative of the formal infinity chart. -/
noncomputable def representative (W : WeierstrassCurve R) (t : MvPowerSeries σ R) :
    Fin 3 → MvPowerSeries σ R := ![t, -1, coordinate W t]

/-- The chart equation is exactly the homogeneous Weierstrass equation. -/
theorem projective_equation_iff (W : WeierstrassCurve R) (t s : R) :
    W.toProjective.Equation ![t, -1, s] ↔ Equation W t s := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, neg_one_sq, one_mul, mul_neg, mul_one]
  unfold Equation
  constructor <;> intro h <;> linear_combination h

/-- A formal chart representative lies on the actual projective cubic. -/
theorem equation_representative (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (curve W).toProjective.Equation (representative W t) :=
  (projective_equation_iff _ _ _).mpr (equation_coordinate W ht)

/-- The Z-partial derivative is one at the origin of the formal chart. -/
theorem constantCoeff_projectiveDerivative (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (MvPolynomial.eval (representative W t) (curve W).toProjective.polynomialZ).constantCoeff =
      1 := by
  rw [WeierstrassCurve.Projective.eval_polynomialZ]
  simp [representative, curve, ht, constantCoeff_coordinate W ht]

/-- The chart has a unit partial derivative over every coefficient ring. -/
theorem isUnit_projectiveDerivative (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    IsUnit (MvPolynomial.eval (representative W t) (curve W).toProjective.polynomialZ) :=
  MvPowerSeries.isUnit_iff_constantCoeff.mpr
    (constantCoeff_projectiveDerivative W ht ▸ isUnit_one)

/-- Formal chart representatives satisfy Mathlib's nonsingularity predicate. -/
theorem nonsingular_representative [Nontrivial R] (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (curve W).toProjective.Nonsingular (representative W t) :=
  ⟨equation_representative W ht, Or.inr (Or.inr (isUnit_projectiveDerivative W ht).ne_zero)⟩

open scoped WeierstrassCurve.Projective in
/-- The fixed middle coordinate makes the formal parameter projectively unique. -/
theorem representative_equiv_iff (W : WeierstrassCurve R) (t v : MvPowerSeries σ R) :
    representative W t ≈ representative W v ↔ t = v := by
  constructor
  · rintro ⟨u, h⟩
    have hy := congrFun h 1
    have hx := congrFun h 0
    have hu : (u : MvPowerSeries σ R) = 1 := by
      simpa [representative, Units.smul_def] using hy
    simpa [representative, Units.smul_def, hu] using hx.symm
  · rintro rfl
    exact Setoid.refl _

/-- The point defined by a zero-constant formal parameter. -/
noncomputable def projectivePoint [Nontrivial R] (W : WeierstrassCurve R)
    (t : {t : MvPowerSeries σ R // t.constantCoeff = 0}) : (curve (σ := σ) W).toProjective.Point :=
  ⟨(WeierstrassCurve.Projective.nonsingularLift_iff _).mpr
    (nonsingular_representative W t.property)⟩

/-- The map from formal parameters to actual projective points is injective. -/
theorem projectivePoint_injective [Nontrivial R] (W : WeierstrassCurve R) :
    Function.Injective (projectivePoint (σ := σ) W) := by
  intro t v h
  apply Subtype.ext
  exact (representative_equiv_iff W _ _).mp
    (Quotient.exact (congrArg WeierstrassCurve.Projective.Point.point h))

end FLT.Mazur.FormalInfinity
