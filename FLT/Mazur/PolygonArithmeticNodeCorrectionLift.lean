/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLaurentCorrectionLift
public import FLT.Mazur.PolygonSmoothingNilpotentBoundaryFactor

/-!
# Whole-node correction lifts at successive arithmetic orders

One integral Laurent field yields full node isomorphisms at every arithmetic
order. Both coordinates and the changed smoothing descend under the actual
arithmetic quotient maps. The first layer recovers the original shear.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonSmoothing LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- The smoothing after a correction, including its scalar drift at the given order. -/
def correctionSmoothing (m : ℕ) (t : Quotient R π m) (q : R[T;T⁻¹]) : Quotient R π m :=
  (1 + parameter R π m * algebraMap R (Quotient R π m) (q.coeff 1)) * t

/-- The actual whole-node isomorphism, with finite inverse at every arithmetic order. -/
irreducible_def correctionNodeFactor (m : ℕ) (t : Quotient R π m) (q : R[T;T⁻¹]) :
    ChartRing (correctionSmoothing R π m t q) ≃ₐ[Quotient R π m] ChartRing t :=
  nilpotentShearEquiv t (parameter R π m) ⟨m + 1, parameter_pow R π m⟩
    (algebraMap R (Quotient R π m) (q.coeff 1))
    (LaurentBoundaryCorrectionSplit.boundaryLift t (correctionField R π m q))

/-- Arithmetic restriction preserves the exact changed smoothing. -/
theorem correctionSmoothing_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : R[T;T⁻¹]) :
    restriction R π m (correctionSmoothing R π (m + 1) t q) =
      correctionSmoothing R π m s q := by
  simp only [correctionSmoothing, map_mul, map_add, map_one, restriction_parameter,
    AlgHom.commutes, hs]

/-- The full node factors, with all polynomial tails, form a quotient-compatible family. -/
theorem correctionNodeFactor_restriction (m : ℕ) (t : Quotient R π (m + 1))
    (s : Quotient R π m) (hs : restriction R π m t = s) (q : R[T;T⁻¹]) :
    (ringMap (restriction R π m).toRingHom t s hs).comp
        (correctionNodeFactor R π (m + 1) t q).toAlgHom.toRingHom =
      (correctionNodeFactor R π m s q).toAlgHom.toRingHom.comp
        (ringMap (restriction R π m).toRingHom
          (correctionSmoothing R π (m + 1) t q) (correctionSmoothing R π m s q)
          (correctionSmoothing_restriction R π m t s hs q)) := by
  rw [correctionNodeFactor_def, correctionNodeFactor_def]
  unfold correctionSmoothing
  let F := ringMap (restriction R π m).toRingHom t s hs
  let p := LaurentBoundaryCorrectionSplit.boundaryLift t (correctionField R π (m + 1) q)
  let r := LaurentBoundaryCorrectionSplit.boundaryLift s (correctionField R π m q)
  have hp : F p = r := by
    exact (boundaryLift_ringMap _ _ _ _ _).trans
      (congrArg (LaurentBoundaryCorrectionSplit.boundaryLift s)
        (correctionField_restriction R π m q))
  have hv : Units.map F
      (nilpotentChartMultiplier t (parameter R π (m + 1))
        ⟨m + 2, parameter_pow R π (m + 1)⟩ p) =
      nilpotentChartMultiplier s (parameter R π m) ⟨m + 1, parameter_pow R π m⟩ r := by
    apply Units.ext
    change F (↑(nilpotentChartMultiplier t (parameter R π (m + 1))
      ⟨m + 2, parameter_pow R π (m + 1)⟩ p) : ChartRing t) = _
    rw [nilpotentChartMultiplier_val, nilpotentChartMultiplier_val, RingHom.map_add,
      map_one, map_mul, hp]
    congr 2
    exact (ringMap_scalar _ _ _ _ _).trans
      (congrArg (algebraMap (Quotient R π m) (ChartRing s)) (restriction_parameter R π m))
  have hi := congrArg (fun v : (ChartRing s)ˣ ↦ (↑v⁻¹ : ChartRing s)) hv
  rw [← map_inv] at hi
  apply chartRing_ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, nilpotentShearEquiv_left, map_mul, RingHom.map_add,
      map_one, ringMap_left, ringMap_scalar]
    change leftCoordinate s * (1 + algebraMap _ _
      (restriction R π m (parameter R π (m + 1))) * F p) = _
    rw [restriction_parameter, hp]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, nilpotentShearEquiv_right, map_mul, ringMap_scalar, ringMap_right]
    change algebraMap _ _ (restriction R π m
      (1 + parameter R π (m + 1) * algebraMap R _ (q.coeff 1))) *
      (rightCoordinate s * F (↑(nilpotentChartMultiplier t _ _ p)⁻¹)) = _
    rw [map_add, map_one, map_mul, restriction_parameter, AlgHom.commutes]
    exact congrArg (fun z : ChartRing s ↦
      algebraMap (Quotient R π m) (ChartRing s)
        (1 + parameter R π m * algebraMap R _ (q.coeff 1)) * (rightCoordinate s * z)) hi


/-- The first-order smoothing identifies with the original one when annihilated by π. -/
theorem correctionSmoothing_first (t : Quotient R π 1)
    (ht : parameter R π 1 * t = 0) (q : R[T;T⁻¹]) :
    correctionSmoothing R π 1 t q = t :=
  nilpotentShear_parameter_eq t (parameter R π 1) ht _

/-- At first order the entire factor is the original node shear, not just its boundary. -/
theorem correctionNodeFactor_first (t : Quotient R π 1)
    (ht : parameter R π 1 * t = 0) (q : R[T;T⁻¹]) :
    (correctionNodeFactor R π 1 t q).toAlgHom.toRingHom =
      (squareZeroShear t (parameter R π 1) ht
        (LaurentBoundaryCorrectionSplit.boundaryLift t (correctionField R π 1 q))).toRingHom.comp
        (ringMap (RingHom.id _) (correctionSmoothing R π 1 t q) t
          (correctionSmoothing_first R π t ht q)) := by
  rw [correctionNodeFactor_def]
  unfold correctionSmoothing
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar, RingHom.id_apply]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, nilpotentShearEquiv_left, ringMap_left, squareZeroShear_left]
    ring
  · have hp := boundaryLift_weighted_right t (parameter R π 1) ht (correctionField R π 1 q)
    rw [correctionField_coeff] at hp
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, ringMap_right, squareZeroShear_right]
    exact nilpotentShearEquiv_right_fixed t (parameter R π 1) _ _ _ hp

end FLT.Mazur.PolygonArithmeticStages
