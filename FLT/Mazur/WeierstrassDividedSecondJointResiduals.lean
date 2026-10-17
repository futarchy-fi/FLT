/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointIdentification
public import FLT.Mazur.WeierstrassDividedSecondResidualAlgebra

/-!
# Simultaneous cancellation of second incoming and closing errors

The shared retained correction uses both full boundary fields. The preceding
node supplies the remaining positive incoming field. Their exact Laurent
compositions cancel all four errors at the second layer.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentBoundaryVectorField
open LaurentPolynomial

/-- Reciprocal vector fields commute with additive inversion. -/
theorem reciprocalField_neg {S : Type*} [CommRing S] (q : S[T;T⁻¹]) :
    reciprocalField (-q) = -reciprocalField q := by
  ext k
  simp only [reciprocalField_coeff, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]

end FLT.Mazur.LaurentBoundaryVectorField

namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "V" => arithmeticSecondJointRetainedIntegralField hπ data H j hj u hu

/-- Both substitutions on the shared retained node in the original inverse edge coordinate. -/
def arithmeticSecondJointEdgeEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m τ (V b) a)).trans invert

/-- The actual full outgoing substitution of the preceding node correction. -/
def arithmeticSecondPrecedingPuncture (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  correctionPunctureFactor R π m τ (arithmeticSecondPrecedingIntegralField hπ data H j hj u hu b)
    true

/-- The full incoming residual formula after simultaneous endpoint corrections. -/
def arithmeticSecondJointIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticSecondJointEdgeEquiv hπ data H m j hj u hu b false).trans
      (arithmeticResidualLiftEdgeEquiv hπ data H m j hj u hu b false)).trans
    (arithmeticSecondPrecedingPuncture hπ data H m j hj u hu b).symm

/-- The closing residual uses the same retained node as the incoming residual. -/
def arithmeticSecondJointClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticSecondResidualLiftTerminalPuncture hπ data H m j hj u hu b).symm.trans
      (arithmeticResidualLiftClosingEquiv hπ data H m j hj u hu b)).trans
    (arithmeticSecondJointEdgeEquiv hπ data H m j hj u hu b true).symm

omit m in
/-- The new shared-node outgoing map retains the complete previously identified closing factor. -/
theorem arithmeticSecondJointEdgeEquiv_outgoing_second (b : Bool) :
    arithmeticSecondJointEdgeEquiv hπ data H 2 j hj u hu b true =
      arithmeticSecondResidualLiftEdgeEquiv hπ data H 2 j hj u hu b true := by
  rw [arithmeticSecondJointEdgeEquiv, arithmeticSecondJointRetainedPuncture_second,
    arithmeticSecondJointRetainedLayerField_outgoing, arithmeticSecondResidualLiftEdgeEquiv,
    arithmeticSecondResidualLiftRetainedPuncture_second]

omit m in
/-- The preceding full puncture supplies exactly the positive incoming field at layer two. -/
theorem arithmeticSecondPrecedingPuncture_second (b : Bool) :
    arithmeticSecondPrecedingPuncture hπ data H 2 j hj u hu b =
      LaurentSquareZeroAutomorphism.equiv (parameter R π 2 ^ 2)
        (nextCorrectionParameter_square R π 1)
        (positivePart (arithmeticSecondResidualField hπ data H j hj u hu true b)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 2 _ (higherCorrectionField R π 1 _) true (T 1) = _
  rw [correctionPunctureFactor_higher_coordinate R π 2 1 _ _
    (fun d hd ↦ by rw [positivePart_coeff, ite_eq_right (by omega)]),
    correctionField_positive, arithmeticSecondResidualIntegralField_spec]
  exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm

omit m in
/-- After the shared opposite correction only the predecessor's positive incoming map remains. -/
theorem arithmeticSecondJointIncoming_factorization (b : Bool) :
    (arithmeticSecondJointEdgeEquiv hπ data H 2 j hj u hu b false).trans
        (arithmeticResidualLiftEdgeEquiv hπ data H 2 j hj u hu b false) =
      arithmeticSecondPrecedingPuncture hπ data H 2 j hj u hu b := by
  rw [arithmeticSecondJointEdgeEquiv, arithmeticSecondJointRetainedPuncture_second,
    arithmeticSecondJointRetainedLayerField_incoming, arithmeticSecondPrecedingPuncture_second]
  apply AlgEquiv.coe_toAlgHom_injective
  have hh := arithmeticSecondResidualField_subst hπ data H j hj u hu true b
  change (arithmeticResidualLiftEdgeEquiv hπ data H 2 j hj u hu b false).toAlgHom = _ at hh
  change (arithmeticResidualLiftEdgeEquiv hπ data H 2 j hj u hu b false).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [hh, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticSecondResidualField hπ data H j hj u hu true b)
  linear_combination -hp

omit m in
/-- Both incoming errors vanish as full Laurent maps after the simultaneous endpoint corrections. -/
theorem arithmeticSecondJointIncomingEquiv_second (b : Bool) :
    arithmeticSecondJointIncomingEquiv hπ data H 2 j hj u hu b = AlgEquiv.refl := by
  unfold arithmeticSecondJointIncomingEquiv
  rw [arithmeticSecondJointIncoming_factorization]
  apply AlgEquiv.ext
  intro z
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

omit m in
/-- Both closing errors vanish with those same shared retained corrections. -/
theorem arithmeticSecondJointClosingEquiv_second (b : Bool) :
    arithmeticSecondJointClosingEquiv hπ data H 2 j hj u hu b = AlgEquiv.refl := by
  unfold arithmeticSecondJointClosingEquiv
  rw [arithmeticSecondJointEdgeEquiv_outgoing_second]
  exact arithmeticSecondResidualClosingEquiv_second hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
