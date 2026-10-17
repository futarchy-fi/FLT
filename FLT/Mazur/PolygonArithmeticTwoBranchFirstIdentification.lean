/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTwoBranchCorrectionLift
public import FLT.Mazur.PolygonSmoothingIdentificationCalculus
public import FLT.Mazur.PolygonSmoothingSquareZeroTwoBranches

/-!
# First-order identification of the full two-branch lift

The common source identification passes through both corrections, including
reflection. The resulting equality holds on the whole nonreduced node.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)
local notation "Q" => Quotient R π 1
local notation "e" => parameter R π 1

/-- A positive field lift recovers the full reflected first-order factor. -/
theorem reflectedCorrectionNodeFactor_first (t : Q) (ht : e * t = 0)
    (q : R[T;T⁻¹]) (p : Q[T;T⁻¹]) (hp : correctionField R π 1 q = positivePart p) :
    (reflectedCorrectionNodeFactor R π 1 t q).toAlgHom.toRingHom =
      (squareZeroReflectedFactor t e (parameter_pow R π 1) ht p).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q) (correctionSmoothing R π 1 t q) t
          (correctionSmoothing_first R π t ht q)) := by
  rw [reflectedCorrectionNodeFactor_def, squareZeroReflectedFactor_def]
  have h := correctionNodeFactor_first R π t ht q
  rw [hp] at h
  exact nodeIdentification_reflect _ t (correctionSmoothing_first R π t ht q)
    _ (squareZeroPositiveFactor t e (parameter_pow R π 1) ht p).toAlgHom.toRingHom h

/-- Both first-order corrections recover the original common whole-node automorphism. -/
theorem twoBranchCorrectionNodeFactor_first (t : Q) (ht : e * t = 0)
    (q : Bool → R[T;T⁻¹]) (p : Bool → Q[T;T⁻¹])
    (hp : ∀ b, correctionField R π 1 (q b) = positivePart (p b)) :
    (twoBranchCorrectionNodeFactor R π 1 t q).toAlgHom.toRingHom =
      (squareZeroTwoBranchFactor t e (parameter_pow R π 1) ht p).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id Q) (twoBranchCorrectionSmoothing R π 1 t q) t
          (twoBranchCorrectionSmoothing_first R π t ht q)) := by
  let s := correctionSmoothing R π 1 t (q false)
  have hs : s = t := correctionSmoothing_first R π t ht (q false)
  have hes : e * s = 0 := by rw [hs]; exact ht
  have hF := correctionNodeFactor_first R π s hes (q true)
  rw [hp true] at hF
  have hG := reflectedCorrectionNodeFactor_first R π t ht (q false) (p false) (hp false)
  have hN := nodeIdentification_square (fun z : Q ↦ e * z = 0)
    (fun z hz ↦ (squareZeroPositiveFactor z e (parameter_pow R π 1) hz
      (p true)).toAlgHom.toRingHom) s t hs hes ht
  rw [twoBranchCorrectionNodeFactor_def, squareZeroTwoBranchFactor_def]
  change ((reflectedCorrectionNodeFactor R π 1 t (q false)).toAlgHom.toRingHom).comp
    (correctionNodeFactor R π 1 s (q true)).toAlgHom.toRingHom = _
  rw [hG, hF]
  change (RingHom.comp _ (ringMap (RingHom.id Q) s t hs)).comp
    ((squareZeroPositiveFactor s e (parameter_pow R π 1) hes
      (p true)).toAlgHom.toRingHom.comp _) = _
  rw [RingHom.comp_assoc, ← RingHom.comp_assoc _ _ (ringMap (RingHom.id Q) s t hs),
    hN, RingHom.comp_assoc, nodeIdentification_comp, ← RingHom.comp_assoc]
  rfl

end FLT.Mazur.PolygonArithmeticStages
