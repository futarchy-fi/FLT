/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEarlierNodes
public import FLT.Mazur.WeierstrassDividedFifthShallowIncomingCancellation
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Cancellation at both ends of the fifth outer retained chain

The last factor is shared with the closing edge. The farther factor is shared
with the outer incoming edge and cancels the full old farther compensation.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthIncomingEquiv arithmeticFourthFartherIncomingEquiv
  arithmeticFifthResidualField arithmeticFifthPairedIntegralField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "s" => arithmeticFifthDeepInput hπ data H j hj u hu
local notation "P" => fun v ↦ arithmeticFifthPairedIntegralField hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v)
local notation "C" => fun v m b ↦ arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v m b) b
local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu

/-- The shared incoming residual uses the same last factor as the full fifth closing edge. -/
def arithmeticFifthDeepIncomingEquiv (m : ℕ) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  ((arithmeticFifthShallowLastEdgeEquiv hπ data H j hj u hu m b false).trans
      (arithmeticFourthIncomingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s .predecessor m b)
      (P .predecessor b) true).symm

/-- The full farther residual uses the same farther factor as the outer incoming edge. -/
def arithmeticFifthDeepFartherIncomingEquiv (m : ℕ) (b : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  ((C .farther m b).trans
      (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu m b)).trans
    (correctionPunctureFactor R π m (τ m) (A b) true).symm

/-- Changing the predecessor's opposite field preserves the full incoming cancellation. -/
theorem arithmeticFifthDeepIncomingEquiv_fifth (b : Bool) :
    arithmeticFifthDeepIncomingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthDeepIncomingEquiv
  rw [arithmeticFifthShallowIncoming_factorization, arithmeticFifthShallowPrecedingPuncture_fifth,
    arithmeticFifthDeepPuncture_fifth]
  have hout := arithmeticFifthShallowPrecedingLayerField_outgoing hπ data H j hj u hu b
  dsimp only at hout
  rw [hout, arithmeticFifthPairedField_outgoing, fifthDeepOutgoing]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

/-- The full farther compensation leaves precisely the next earlier positive factor. -/
theorem arithmeticFifthDeepFartherIncoming_factorization (b : Bool) :
    (C .farther 5 b).trans (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu 5 b) =
      correctionPunctureFactor R π 5 (τ 5) (A b) true := by
  dsimp only
  rw [arithmeticFifthPairedEdgeEquiv,
    arithmeticFifthPairedPuncture_fifth hπ data H j hj u hu
      (fifthDeepOutgoing .farther) (fifthDeepIncoming .farther) (s .farther 5 b)
      (arithmeticFifthDeepInput_annihilated hπ data H j hj u hu .farther 5 b),
    arithmeticFifthPairedField_incoming, fifthDeepIncoming,
    arithmeticFifthDeepEarlierPuncture_fifth]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFifthResidualField_subst hπ data H j hj u hu .fartherIncoming b
  change (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom = _ at h
  change (arithmeticFourthFartherIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFifthResidualField hπ data H j hj u hu .fartherIncoming b)
  linear_combination -hp

/-- The whole farther incoming residual is identity at the fifth layer. -/
theorem arithmeticFifthDeepFartherIncomingEquiv_fifth (b : Bool) :
    arithmeticFifthDeepFartherIncomingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthDeepFartherIncomingEquiv
  rw [arithmeticFifthDeepFartherIncoming_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
