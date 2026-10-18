/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdRestriction

/-!
# Full relative residuals after the third depth-zero correction

Both initial and closing residuals use the same installed node inputs. Their
complete coefficient quotients and third-layer identities supply the next fields.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroSecondClosingEquiv arithmeticZeroThirdLastEdgeEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "L" => arithmeticZeroThirdLastEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticZeroThirdClosingEquiv hπ data H j hj u hu

/-- Remove only the entire original initial base to measure the new relative error. -/
def arithmeticZeroThirdInitialRelativeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticZeroThirdInitialEquiv hπ data H j hj u hu m b).trans
    (arithmeticInitialBaseEquiv data H m j hj).symm

local notation "D" => arithmeticZeroThirdInitialRelativeEquiv hπ data H j hj u hu

/-- The same last factor retains its full outgoing quotient in the closing coordinate. -/
theorem arithmeticZeroThirdLastEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (L (m + 1) b).toRingHom =
      (L m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroThirdLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticZeroSecondLastSmoothing_restriction hπ data H j hj u hu m b) _ true
  · exact punctureEquiv_invert_naturality f

/-- The new full closing residual respects the original coefficient quotient. -/
theorem arithmeticZeroThirdClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroThirdClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact symm_naturality f _ _
        (twoBranchCorrectionRebasedPunctureFactor_restriction R π m _ _
          (arithmeticZeroSecondTerminalSmoothing_restriction hπ data H j hj u hu m) _ b)
    · exact arithmeticZeroSecondClosingEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _
      (arithmeticZeroThirdLastEdgeEquiv_restriction hπ data H j hj u hu m b)

/-- The entire relative initial residual retains every coefficient quotient. -/
theorem arithmeticZeroThirdInitialRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroThirdInitialRelativeEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticZeroThirdInitialEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _ (arithmeticInitialBaseEquiv_restriction data H m j hj)

omit m in
/-- The full relative initial error vanishes at layer three. -/
theorem arithmeticZeroThirdInitialRelativeEquiv_third (b : Bool) : D 3 b = AlgEquiv.refl := by
  rw [arithmeticZeroThirdInitialRelativeEquiv, arithmeticZeroThirdInitialEquiv_third]
  ext z : 1
  exact (arithmeticInitialBaseEquiv data H 3 j hj).symm_apply_apply z

end FLT.Mazur.WeierstrassDividedDepth
