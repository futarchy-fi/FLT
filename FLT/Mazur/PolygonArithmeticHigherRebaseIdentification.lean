/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTwoBranchRebase
public import FLT.Mazur.PolygonArithmeticHigherTwoBranchIdentification

/-!
# Higher-layer recovery after rebasing the whole terminal correction

Both source identifications cancel explicitly. Thus rebasing preserves the
original higher-order factor and permits its correctly directed geometric inverse.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m r : ℕ)
local notation "Q" => Quotient R π m
local notation "e" => parameter R π m ^ (r + 1)
local notation "v" => higherCorrectionField R π r

/-- Rebasing preserves the annihilated higher-layer smoothing. -/
theorem twoBranchCorrectionRebasedSmoothing_higher_eq (t : Q) (ht : e * t = 0)
    (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionRebasedSmoothing R π m t (fun b ↦ v (q b)) = t := by
  have hv : ↑(twoBranchCorrectionDriftUnit R π m (fun b ↦ v (q b))) * t = t := by
    rw [← twoBranchCorrectionSmoothing_eq_drift,
      twoBranchCorrectionSmoothing_higher_eq R π m r t ht]
  unfold twoBranchCorrectionRebasedSmoothing
  calc
    _ = ↑(twoBranchCorrectionDriftUnit R π m (fun b ↦ v (q b)))⁻¹ *
        (↑(twoBranchCorrectionDriftUnit R π m (fun b ↦ v (q b))) * t) := by rw [hv]
    _ = t := by rw [← mul_assoc, Units.inv_mul, one_mul]

variable (he : (parameter R π m ^ (r + 1)) ^ 2 = 0)
include he

/-- The rebased factor recovers the complete original higher-order correction. -/
theorem twoBranchCorrectionRebasedFactor_higher_eq (t : Q) (ht : e * t = 0)
    (q : Bool → R[T;T⁻¹]) (p : Bool → Q[T;T⁻¹])
    (hp : ∀ b, correctionField R π m (q b) = positivePart (p b)) :
    (ringMap (RingHom.id Q) (twoBranchCorrectionRebasedSmoothing R π m t (fun b ↦ v (q b))) t
        (twoBranchCorrectionRebasedSmoothing_higher_eq R π m r t ht q)).comp
      (twoBranchCorrectionRebasedFactor R π m t (fun b ↦ v (q b))).toAlgHom.toRingHom =
        (squareZeroTwoBranchFactor t e he ht p).toAlgHom.toRingHom := by
  let s := twoBranchCorrectionRebasedSmoothing R π m t (fun b ↦ v (q b))
  have hs : s = t := twoBranchCorrectionRebasedSmoothing_higher_eq R π m r t ht q
  have hes : e * s = 0 := by rw [hs]; exact ht
  have hF := twoBranchCorrectionNodeFactor_higher_eq R π m r he s hes q p hp
  have hN := nodeIdentification_square (fun z : Q ↦ e * z = 0)
    (fun z hz ↦ (squareZeroTwoBranchFactor z e he hz p).toAlgHom.toRingHom)
    s t hs hes ht
  rw [twoBranchCorrectionRebasedFactor_def]
  change (ringMap (RingHom.id Q) s t hs).comp
    ((twoBranchCorrectionNodeFactor R π m s (fun b ↦ v (q b))).toAlgHom.toRingHom.comp
      (nodeParameterEquiv t _ _).toAlgHom.toRingHom) = _
  rw [nodeParameterEquiv_toRingHom, hF, ← RingHom.comp_assoc,
    ← RingHom.comp_assoc, hN, RingHom.comp_assoc, nodeIdentification_comp,
    RingHom.comp_assoc, nodeIdentification_comp, ringMap_id, RingHom.comp_id]

end FLT.Mazur.PolygonArithmeticStages
