/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization

/-!
# Units on both ordinary chart families

The specialized denominator is either the secant difference or the tangent
ordinate sum. This disjunction allows all ordinary outer charts in triple sums.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Every ordinary chart provides one of the two denominators needed for associativity. -/
theorem ordinarySpecialization_denominator_unit (b : Bool)
    (f : additionChartRing W (ordinaryIndex b) →ₐ[R] S) :
    IsUnit (f (ordinaryInputLeft W b (coord W 2 0)) -
      f (ordinaryInputRight W b (coord W 2 0))) ∨
    IsUnit (f (ordinaryInputLeft W b (coord W 2 1)) +
      f (ordinaryInputRight W b (coord W 2 1)) +
      algebraMap R S W.a₁ * f (ordinaryInputRight W b (coord W 2 0)) +
      algebraMap R S W.a₃) := by
  cases b with
  | false => exact Or.inl (ordinarySpecialization_secant_unit W f)
  | true =>
    right
    simpa only [ordinaryInputLeft, ordinaryInputRight, AlgHom.comp_apply,
      productX₂, productY₁, productY₂, ite_true, tangentDenominator,
      map_add, map_mul, AlgHom.commutes] using
      (ordinaryChartDenominator_isUnit W true).map f

end FLT.Mazur.WeierstrassIntegralChart
