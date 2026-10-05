/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAdditionComparison

/-!
# Formal chart points under arbitrary evaluation

The unit partial derivative survives every ring map to a field. Thus evaluation
need not be injective to define a nonsingular point or to compare secants whose
evaluated parameters differ.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {σ : Type*} {K : Type*} [Field K]
variable (W : WeierstrassCurve R) (f : MvPowerSeries σ R →+* K)

/-- A unit derivative guarantees nonsingularity after arbitrary evaluation. -/
theorem nonsingular_evaluation {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    ((curve W).map f).toProjective.Nonsingular (f ∘ representative W t) := by
  constructor
  · rw [WeierstrassCurve.Projective.equation_iff] at *
    have h := congrArg f ((equation_iff _).mp (equation_representative W ht))
    simpa only [Function.comp_apply, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      map_add, map_mul, map_pow, map_sub, map_zero] using h
  · right; right
    have h := ((isUnit_projectiveDerivative W ht).map f).ne_zero
    rwa [map_polynomialZ, MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp]

/-- The evaluated normalized chart point, without an injectivity hypothesis. -/
noncomputable def evaluationPoint (t : MvPowerSeries σ R) (ht : t.constantCoeff = 0) :
    ((curve W).map f).toProjective.Point :=
  ⟨(nonsingularLift_iff _).mpr (nonsingular_evaluation W f ht)⟩

/-- Equality of evaluated points implies equality of their normalized parameters. -/
theorem evaluationPoint_parameter {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0)
    (h : evaluationPoint W f t ht = evaluationPoint W f v hv) : f t = f v := by
  obtain ⟨u, hu⟩ := Quotient.exact (congrArg Point.point h)
  have hy := congrFun hu 1
  have hx := congrFun hu 0
  have hu1 : (u : K) = 1 := by
    simpa [representative, Function.comp_apply, Units.smul_def] using hy
  simpa [representative, Function.comp_apply, Units.smul_def, hu1] using hx.symm

/-- The secant scale survives evaluation when the parameter values differ. -/
theorem evaluation_additionScale_ne_zero {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (hne : f t ≠ f v) :
    f (additionScale W t v) ≠ 0 := by
  have hl := (MvPowerSeries.isUnit_iff_constantCoeff.mpr
    (constantCoeff_cubicLeading W ht hv ▸ isUnit_one)).map f
  have hn := (MvPowerSeries.isUnit_iff_constantCoeff.mpr
    (constantCoeff_negationDenominator W (constantCoeff_thirdParameter W ht hv) ▸
      isUnit_one)).map f
  simpa only [additionScale, map_mul, map_neg, map_pow, map_sub] using
    mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 3 (sub_ne_zero.mpr hne))
      hl.ne_zero)) hn.ne_zero

/-- Arbitrary evaluation preserves addition at distinct evaluated parameters. -/
theorem evaluationPoint_add_of_ne {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) (hne : f t ≠ f v) :
    evaluationPoint W f (add W t v) (constantCoeff_add W ht hv) =
      evaluationPoint W f t ht + evaluationPoint W f v hv := by
  have hp : ¬ f ∘ representative W t ≈ f ∘ representative W v := by
    intro h
    exact hne (evaluationPoint_parameter W f ht hv (Point.ext (Quotient.sound h)))
  have he := congrArg (fun p : Fin 3 → MvPowerSeries σ R => f ∘ p)
    (addXYZ_representative W ht hv)
  rw [← map_addXYZ, comp_smul] at he
  apply Point.ext
  change (⟦f ∘ representative W (add W t v)⟧ : PointClass K) =
    ((curve W).map f).toProjective.addMap ⟦f ∘ representative W t⟧ ⟦f ∘ representative W v⟧
  rw [addMap_eq, add_of_not_equiv hp, he,
    smul_eq _ (evaluation_additionScale_ne_zero W f ht hv hne).isUnit]

end FLT.Mazur.FormalInfinity
