/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTwoBranchRebase

/-!
# First-layer recovery after rebasing the whole terminal correction

Both source identifications cancel explicitly. Thus rebasing preserves the
original first-order factor and permits its correctly directed geometric inverse.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)
local notation "Q" => Quotient R π 1
local notation "e" => parameter R π 1

/-- The rebased factor recovers the complete original first-order correction. -/
theorem twoBranchCorrectionRebasedFactor_first (t : Q) (ht : e * t = 0)
    (q : Bool → R[T;T⁻¹]) (p : Bool → Q[T;T⁻¹])
    (hp : ∀ b, correctionField R π 1 (q b) = positivePart (p b)) :
    (ringMap (RingHom.id Q) (twoBranchCorrectionRebasedSmoothing R π 1 t q) t
        (twoBranchCorrectionRebasedSmoothing_first R π t ht q)).comp
      (twoBranchCorrectionRebasedFactor R π 1 t q).toAlgHom.toRingHom =
        (squareZeroTwoBranchFactor t e (parameter_pow R π 1) ht p).toAlgHom.toRingHom := by
  let s := twoBranchCorrectionRebasedSmoothing R π 1 t q
  have hs : s = t := twoBranchCorrectionRebasedSmoothing_first R π t ht q
  have hes : e * s = 0 := by rw [hs]; exact ht
  have hF := twoBranchCorrectionNodeFactor_first R π s hes q p hp
  have hN := nodeIdentification_square (fun z : Q ↦ e * z = 0)
    (fun z hz ↦ (squareZeroTwoBranchFactor z e (parameter_pow R π 1) hz p).toAlgHom.toRingHom)
    s t hs hes ht
  rw [twoBranchCorrectionRebasedFactor_def]
  change (ringMap (RingHom.id Q) s t hs).comp
    ((twoBranchCorrectionNodeFactor R π 1 s q).toAlgHom.toRingHom.comp
      (nodeParameterEquiv t _ _).toAlgHom.toRingHom) = _
  rw [nodeParameterEquiv_toRingHom, hF, ← RingHom.comp_assoc,
    ← RingHom.comp_assoc, hN, RingHom.comp_assoc, nodeIdentification_comp,
    RingHom.comp_assoc, nodeIdentification_comp, ringMap_id, RingHom.comp_id]

end FLT.Mazur.PolygonArithmeticStages
