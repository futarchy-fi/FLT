/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondPunctureIdentification

/-!
# Full residuals after the actual second closing correction

The complete closing residual uses contravariant composition. At stage two
it is identity. The incoming transition is composed with the new opposite
puncture and is retained explicitly, rather than discarded.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "A" => arithmeticSecondResidualLiftRetainedPuncture hπ data H m j hj u hu
local notation "S" => arithmeticSecondResidualLiftTerminalPuncture hπ data H m j hj u hu

/-- Both new retained substitutions in the original inverse edge coordinate. -/
def arithmeticSecondResidualLiftEdgeEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (A b a)).trans invert

local notation "K" => arithmeticSecondResidualLiftEdgeEquiv hπ data H m j hj u hu

/-- The full closing error after the second correction, in the correct algebra order. -/
def arithmeticSecondResidualClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((S b).symm.trans (arithmeticResidualLiftClosingEquiv hπ data H m j hj u hu b)).trans
    (K b true).symm

/-- The old incoming transition followed geometrically by the new opposite correction. -/
def arithmeticSecondResidualIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (K b false).trans (arithmeticResidualLiftEdgeEquiv hπ data H m j hj u hu b false)

omit m in
/-- The complete old closing residual factors through the two actual second puncture maps. -/
theorem arithmeticSecondResidualClosing_factorization (b : Bool) :
    arithmeticResidualLiftClosingEquiv hπ data H 2 j hj u hu b =
      (arithmeticSecondResidualLiftTerminalPuncture hπ data H 2 j hj u hu b).trans
        (arithmeticSecondResidualLiftEdgeEquiv hπ data H 2 j hj u hu b true) := by
  rw [arithmeticSecondResidualLiftEdgeEquiv,
    arithmeticSecondResidualLiftTerminalPuncture_second,
    arithmeticSecondResidualLiftRetainedPuncture_second]
  apply AlgEquiv.coe_toAlgHom_injective
  rw [show (arithmeticResidualLiftClosingEquiv hπ data H 2 j hj u hu b).toAlgHom =
      LaurentSquareZeroAutomorphism.subst (parameter R π 2 ^ 2)
        (nextCorrectionParameter_square R π 1)
        (arithmeticSecondResidualField hπ data H j hj u hu false b) from
      arithmeticSecondResidualField_subst hπ data H j hj u hu false b]
  change _ = (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
    (reciprocalField (nonpositivePart _))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (parts_add (arithmeticSecondResidualField hπ data H j hj u hu false b)).symm.trans
    (add_comm _ _)

omit m in
/-- Both complete second closing errors vanish at their defining layer. -/
theorem arithmeticSecondResidualClosingEquiv_second (b : Bool) :
    arithmeticSecondResidualClosingEquiv hπ data H 2 j hj u hu b = AlgEquiv.refl := by
  unfold arithmeticSecondResidualClosingEquiv
  rw [arithmeticSecondResidualClosing_factorization]
  apply AlgEquiv.ext
  intro z
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

omit m in
/-- The incoming transition retains exactly its previous full second-layer error. -/
theorem arithmeticSecondResidualIncomingEquiv_second (b : Bool) :
    arithmeticSecondResidualIncomingEquiv hπ data H 2 j hj u hu b =
      arithmeticResidualLiftEdgeEquiv hπ data H 2 j hj u hu b false := by
  unfold arithmeticSecondResidualIncomingEquiv arithmeticSecondResidualLiftEdgeEquiv
  rw [arithmeticSecondResidualLiftRetainedPuncture_opposite_second]
  apply AlgEquiv.ext
  intro z
  simp only [AlgEquiv.trans_apply, AlgEquiv.coe_refl, id_eq]
  exact congrArg (arithmeticResidualLiftEdgeEquiv hπ data H 2 j hj u hu b false)
    (involutive_invert z)

end FLT.Mazur.WeierstrassDividedDepth
