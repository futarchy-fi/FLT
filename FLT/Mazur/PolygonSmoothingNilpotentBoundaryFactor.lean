/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingNilpotentShearNaturality
public import FLT.Mazur.PolygonSmoothingPolynomialShearReduction
public import FLT.Mazur.LaurentBoundaryCorrectionNaturality

/-!
# Full nilpotent lifts of boundary vector fields

A finite boundary field defines an isomorphism of whole smoothing nodes at
any nilpotent order. Its linear coefficient records the smoothing drift.
The construction respects coefficient quotients and recovers the prior
square-zero node factor on the first layer.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial LaurentBoundaryCorrectionSplit
open PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (t e : R) (he : IsNilpotent e)

/-- Lift a boundary field on the full node with its exact scalar smoothing drift. -/
irreducible_def nilpotentBoundaryFactor (q : R[T;T⁻¹]) :
    ChartRing ((1 + e * q.coeff 1) * t) ≃ₐ[R] ChartRing t :=
  nilpotentShearEquiv t e he (q.coeff 1) (LaurentBoundaryCorrectionSplit.boundaryLift t q)

/-- The entire positive outgoing field is retained, without truncation of its tail. -/
theorem nilpotentBoundaryFactor_leftLaurent (q : R[T;T⁻¹])
    (hq : ∀ k : ℤ, k ≤ 0 → q.coeff k = 0) :
    leftLaurentMap t (nilpotentBoundaryFactor t e he q
      (leftCoordinate ((1 + e * q.coeff 1) * t))) = T 1 + C e * q := by
  rw [nilpotentBoundaryFactor_def, nilpotentShearEquiv_left]
  simp only [map_mul, map_add, map_one, AlgHom.commutes, leftLaurentMap_left]
  change T 1 * (1 + C e * leftLaurentMap t
    (LaurentBoundaryCorrectionSplit.boundaryLift t q)) = _
  rw [mul_add, mul_one, mul_left_comm, boundaryLift_value t q hq]

/-- The complete original first-layer correction is recovered on the whole chart. -/
theorem nilpotentBoundaryFactor_squareZero (h2 : e ^ 2 = 0) (het : e * t = 0)
    (q : R[T;T⁻¹]) :
    (nilpotentBoundaryFactor t e he q).toAlgHom.toRingHom =
      (squareZeroShear t e het (LaurentBoundaryCorrectionSplit.boundaryLift t q)).toRingHom.comp
        (ringMap (RingHom.id R) ((1 + e * q.coeff 1) * t) t
          (nilpotentShear_parameter_eq t e het _)) := by
  rw [nilpotentBoundaryFactor_def]
  exact nilpotentShearEquiv_eq_squareZero t e het h2 q

/-- Boundary corrections commute with the full original coefficient quotient maps. -/
theorem nilpotentBoundaryFactor_naturality (f : R →+* S) (s : S) (hs : f t = s)
    (q : R[T;T⁻¹]) :
    (ringMap f t s hs).comp (nilpotentBoundaryFactor t e he q).toAlgHom.toRingHom =
      (nilpotentBoundaryFactor s (f e) (he.map f) (coeffMap f q)).toAlgHom.toRingHom.comp
        (ringMap f ((1 + e * q.coeff 1) * t) ((1 + f e * (coeffMap f q).coeff 1) * s)
          (by rw [coeffMap_coeff]; exact nilpotentShear_parameter_map f t s hs e _)) := by
  rw [nilpotentBoundaryFactor_def, nilpotentBoundaryFactor_def]
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, nilpotentShearEquiv_left, map_mul, RingHom.map_add,
      map_one, ringMap_left, ringMap_scalar, boundaryLift_ringMap]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, nilpotentShearEquiv_right, map_mul, ringMap_scalar,
      ringMap_right, nilpotentChartMultiplier_map_inv, RingHom.map_add, map_one,
      coeffMap_coeff, boundaryLift_ringMap]


end FLT.Mazur.PolygonSmoothing
