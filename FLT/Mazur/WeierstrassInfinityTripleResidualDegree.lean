/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleResidualSystem
public import Mathlib.Tactic.ComputeDegree

/-!
# Degree bounds for the actual residual system

The three auxiliary polynomials are quadratic, so the centered cubic comparison
has only four coefficient equations. The highest equation has no hidden cubic
coefficients, including when leading coefficients vanish or are zero divisors.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

/-- A linear polynomial has degree at most one over any commutative ring. -/
theorem infinity_parameter_linear_degree {S : Type*} [CommRing S] (a b : S) :
    (C a * X + C b).natDegree ≤ 1 := by
  compute_degree!

/-- The divided cubic has degree at most two on four linear polynomial coordinates. -/
theorem infinityCubicDividedZ_natDegree_le {S : Type*} [CommRing S]
    (A : WeierstrassCurve S) (p q r s : S[X])
    (hp : p.natDegree ≤ 1) (hq : q.natDegree ≤ 1)
    (hr : r.natDegree ≤ 1) (hs : s.natDegree ≤ 1) :
    (infinityCubicDividedZ (A.map C) p q r s).natDegree ≤ 2 := by
  unfold infinityCubicDividedZ
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  compute_degree!
  omega

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The first common parameter coordinate has degree at most one. -/
theorem infinityTripleParamXPolynomial_degree (j : Fin 4) :
    (infinityTripleParamXPolynomial W hΔ j).natDegree ≤ 1 := by
  simpa only [infinityTripleParamXPolynomial, map_neg] using
    infinity_parameter_linear_degree
      (-(1 + (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))).a₃ *
        infinityTripleLineIntercept W hΔ j))
      (infinityTripleScalarX W hΔ (infinityTripleOutputIndex j))

/-- The second common parameter coordinate has degree at most one. -/
theorem infinityTripleParamYPolynomial_degree (j : Fin 4) :
    (infinityTripleParamYPolynomial W hΔ j).natDegree ≤ 1 := by
  exact infinity_parameter_linear_degree _ _

/-- Every input factor has degree at most one, without requiring its leading coefficient a unit. -/
theorem infinityTripleParamInputPolynomial_degree (j : Fin 4) (i : Fin 7) :
    (infinityTripleParamInputPolynomial W hΔ j i).natDegree ≤ 1 := by
  have hx := infinityTripleParamXPolynomial_degree W hΔ j
  have hy := infinityTripleParamYPolynomial_degree W hΔ j
  unfold infinityTripleParamInputPolynomial
  compute_degree!

/-- Every actual line remains linear in the common parameter. -/
theorem infinityTripleParamLineZPolynomial_degree (j k : Fin 4) :
    (infinityTripleParamLineZPolynomial W hΔ j k).natDegree ≤ 1 := by
  have hx := infinityTripleParamXPolynomial_degree W hΔ j
  have hy := infinityTripleParamYPolynomial_degree W hΔ j
  unfold infinityTripleParamLineZPolynomial
  compute_degree!

/-- The scaled input pair has degree at most two. -/
theorem infinityTripleParamInputPair_degree (j k : Fin 4) :
    (infinityTripleParamInputPair W hΔ j k).natDegree ≤ 2 := by
  have hl := infinityTripleParamInputPolynomial_degree W hΔ j (infinityTripleLeftIndex k)
  have hr := infinityTripleParamInputPolynomial_degree W hΔ j (infinityTripleRightIndex k)
  unfold infinityTripleParamInputPair
  compute_degree!
  omega

/-- The actual divided correction has degree at most two. -/
theorem infinityTripleParamDividedPolynomial_degree (j k : Fin 4) :
    (infinityTripleParamDividedPolynomial W hΔ j k).natDegree ≤ 2 :=
  infinityCubicDividedZ_natDegree_le
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))) _ _ _ _
    (infinityTripleParamXPolynomial_degree W hΔ j)
    (infinityTripleParamYPolynomial_degree W hΔ j)
    (infinityTripleParamLineZPolynomial_degree W hΔ j j)
    (infinityTripleParamLineZPolynomial_degree W hΔ j k)

/-- The top coefficient equation has no residual cubic terms. -/
theorem infinityTripleParam_residual_coeff_top (j k : Fin 4) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    (infinityTripleParamInputPair W hΔ j j).coeff 2 -
        (1 + A.a₃ * infinityTripleNegLineResidual W hΔ (infinityTripleOutputIndex k) j) *
          (infinityTripleParamInputPair W hΔ j k).coeff 2 =
      infinityTripleLineSeparationSlope W hΔ j k *
        (infinityTripleParamDividedPolynomial W hΔ j k).coeff 2 := by
  have hQ : (infinityTripleParamInputPair W hΔ j k).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (infinityTripleParamInputPair_degree W hΔ j k) (by decide))
  have hD : (infinityTripleParamDividedPolynomial W hΔ j k).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (infinityTripleParamDividedPolynomial_degree W hΔ j k) (by decide))
  simpa only [hQ, hD, mul_zero, add_zero] using
    infinityTripleParam_residual_coeff_succ W hΔ j k 2

end FLT.Mazur.WeierstrassIntegralChart
