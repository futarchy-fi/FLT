/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroPunctures
public import FLT.Mazur.WeierstrassDividedInitialBaseParameter

/-!
# The complete depth-zero initial residual

Keep the entire original base parameter and all four direct last punctures.
The relative residual is precisely their full composition, with no predecessor.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "B" => arithmeticInitialBaseEquiv data H m j hj
local notation "A" => arithmeticFourthAccumulatedLastPuncture hπ data H m j hj u hu

/-- The depth-zero transition retains the full original base after the last factor. -/
def arithmeticFourthZeroInitialEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (A b false).trans B

/-- Remove only the original base when measuring the accumulated initial error. -/
def arithmeticFourthZeroInitialRelativeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticFourthZeroInitialEquiv hπ data H m j hj u hu b).trans (B).symm

/-- The entire relative error is the direct puncture of the same accumulated last factor. -/
theorem arithmeticFourthZeroInitialRelativeEquiv_eq (b : Bool) :
    arithmeticFourthZeroInitialRelativeEquiv hπ data H m j hj u hu b = A b false := by
  ext z : 1
  exact (B).symm_apply_apply _

variable [IsBezout R] (ha : 0 = j)
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthOuterAtlasChart arithmeticFourthAccumulatedLastIso
local notation "ω" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticFourthOuterInitialZeroIdentification hπ data H m j hj u hu ha
local notation "D" => arithmeticFourthOuterLastIdentification hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "N" => arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The normalized initial puncture has this complete residual in the actual global atlas. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_zero_residual (b : Bool) :
    (N).inv ≫ P ≫ (J b).hom ≫ ω (.initial b) =
      (punctureSpecIso (arithmeticFourthZeroInitialEquiv hπ data H m j hj u hu b)).hom ≫
        rightBranchOpen Q τ ≫ (O b).hom ≫ (D b).hom ≫
          ω (.retained ⟨j, by omega⟩ b) := by
  rw [arithmeticFourthOuterAtlas_zero_initial hπ data H m j hj u hu ha b,
    arithmeticInitialNormalizedPunctureIso_inv_comp_assoc]
  simp only [arithmeticFourthZeroInitialEquiv, punctureSpecIso_trans, Iso.trans_hom,
    arithmeticInitialBaseEquiv_spec, Category.assoc]
  have h := arithmeticFourthAccumulatedLastIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc (rightBranchOpen Q τ),
    ← Category.assoc (rightBranchOpen Q τ ≫ (O b).hom), h]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
