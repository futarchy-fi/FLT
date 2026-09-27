/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.InseparableLifting

/-!
# Tate uniformization over a local field

Both symmetric quadratics split over the field of definition of the point.
Combined with the coordinate inversions, this proves surjectivity and makes
the constructed quotient homomorphism an additive equivalence.
-/

@[expose] public section

namespace TateCurve
open ValuativeRel
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
/-- The interior symmetric quadratic splits over the original local field. -/
theorem interior_lift (q : Kˣ) (hq : valuation K (q : K) < 1)
    (x y t : K) (hxy : (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y)
    (ht : valuation K t < 1)
    (hseries : (∑' n : ℕ, xPair ((q : K) ^ (2 * n) * q) ((q : K) ^ n * t)) -
      2 * tateCorrection (q : K) = x) : ∃ u : K, u ^ 2 - t * u + q = 0 := by
  by_cases h2 : (2 : K) = 0
  · by_cases ht0 : t = 0
    · subst t
      exact interior_lift_of_two_eq_zero q hq x y hxy hseries h2
    · exact interior_lift_of_derivative_ne_zero q hq x y t hxy ht hseries (Or.inr ht0)
  · exact interior_lift_of_derivative_ne_zero q hq x y t hxy ht hseries (Or.inl h2)

/-- Every point of the Tate curve over a local field has a uniformization parameter. -/
theorem uniformizationPoint_surjective (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Function.Surjective (uniformizationPoint q hq) :=
  uniformizationPoint_surjective_of_quadratic_lifts q hq
    (fun x y t hxy _ ht he ↦ interior_lift q hq x y t hxy ht he)
    (fun x y z hxy _ hz0 hz he ↦ boundary_lift q hq x y z hxy hz0 hz he)

variable [DecidableEq K]
/-- The convergent Tate uniformization is a group isomorphism over every local field. -/
noncomputable def localUniformization (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Additive (Kˣ ⧸ Subgroup.zpowers q) ≃+ (WeierstrassCurve.tateCurve (q : K)).toAffine.Point :=
  AddEquiv.ofBijective (quotientPointHom q hq)
    ⟨quotientPointHom_injective q hq, fun P ↦ by
      obtain ⟨u, hu⟩ := uniformizationPoint_surjective q hq P
      exact ⟨Additive.ofMul u, hu⟩⟩
end TateCurve
