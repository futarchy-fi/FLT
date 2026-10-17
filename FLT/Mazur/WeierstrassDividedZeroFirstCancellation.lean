/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstPunctures
public import FLT.Mazur.PolygonArithmeticLaurentIdentityRestriction
public import FLT.Mazur.WeierstrassDividedFourthResidualRestriction

/-!
# Simultaneous first cancellation at depth zero

Keep the full original initial base, the same last-node factor on both edges,
and the existing common terminal. Both actual residuals cancel at layer one.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticZeroFirstInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroFirstLastIntegralField hπ data H j hj u hu

/-- The full initial residual after the two actual endpoint factors. -/
def arithmeticZeroFirstInitialEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionPunctureFactor R π m τ (V b) false).trans
      (arithmeticFourthZeroInitialEquiv hπ data H m j hj u hu b)).trans
    (correctionPunctureFactor R π m τ (A b) true).symm

/-- Use the outgoing puncture of that same last factor in the closing coordinate. -/
def arithmeticZeroFirstLastEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m τ (V b) true)).trans invert

/-- Keep the full previous common terminal and the new shared last factor. -/
def arithmeticZeroFirstClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticFourthClosingEquiv hπ data H j hj u hu m b).trans
    (arithmeticZeroFirstLastEdgeEquiv hπ data H j hj u hu m b).symm

omit m in
/-- The complete initial edge equals its original full base at layer one. -/
theorem arithmeticZeroFirstInitialEquiv_first (b : Bool) :
    arithmeticZeroFirstInitialEquiv hπ data H j hj u hu 1 b =
      arithmeticInitialBaseEquiv data H 1 j hj := by
  unfold arithmeticZeroFirstInitialEquiv
  rw [arithmeticZeroFirstInitialPuncture_first, arithmeticZeroFirstLastPuncture_first,
    arithmeticZeroFirstLastField_spec]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π 1) 1
    (nextCorrectionParameter_square R π 0)
  · exact arithmeticInitialBaseEquiv_symm_sub_mem data H 1 j hj
  · change ((Ideal.span {parameter R π 1}).map (algebraMap _ _)) ^ 2 = ⊥
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow R π 1,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    have h := arithmeticFourthZeroFirstField_subst hπ data H j hj u hu b
    change _ = LaurentSquareZeroAutomorphism.subst _ _ _
    simpa only [arithmeticFourthZeroInitialRelativeEquiv, pow_one] using h

/-- The already installed fourth closing identity holds at every earlier arithmetic stage. -/
theorem arithmeticFourthClosingEquiv_of_le_four (hm : m ≤ 4) (b : Bool) :
    arithmeticFourthClosingEquiv hπ data H j hj u hu m b = AlgEquiv.refl := by
  apply AlgEquiv.coe_toAlgHom_injective
  exact laurentSystem_identity_restriction
    (fun r ↦ (arithmeticFourthClosingEquiv hπ data H j hj u hu r b).toAlgHom)
    (fun r ↦ arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu r b) hm
    (congrArg AlgEquiv.toAlgHom (arithmeticFourthClosingEquiv_fourth hπ data H j hj u hu b))

omit m in
/-- Both closing edges still cancel, using the same last factor as the initial edges. -/
theorem arithmeticZeroFirstClosingEquiv_first (b : Bool) :
    arithmeticZeroFirstClosingEquiv hπ data H j hj u hu 1 b = AlgEquiv.refl := by
  rw [arithmeticZeroFirstClosingEquiv, arithmeticFourthClosingEquiv_of_le_four
    hπ data H j hj u hu 1 (by omega), arithmeticZeroFirstLastEdgeEquiv,
    arithmeticZeroFirstLastPuncture_outgoing_first]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.refl_symm,
    AlgEquiv.coe_refl, id_eq, invert_symm]
  exact involutive_invert z

end FLT.Mazur.WeierstrassDividedDepth
