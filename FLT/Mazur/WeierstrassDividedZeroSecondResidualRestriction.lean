/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondRestriction

/-!
# Full relative residuals after the second depth-zero correction

Both initial and closing residuals use the same installed node inputs. Their
complete coefficient quotients and second-layer identities supply the next fields.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroFirstClosingEquiv arithmeticZeroSecondLastEdgeEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "L" => arithmeticZeroSecondLastEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticZeroSecondClosingEquiv hπ data H j hj u hu

/-- Remove only the entire original initial base to measure the new relative error. -/
def arithmeticZeroSecondInitialRelativeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticZeroSecondInitialEquiv hπ data H j hj u hu m b).trans
    (arithmeticInitialBaseEquiv data H m j hj).symm

local notation "D" => arithmeticZeroSecondInitialRelativeEquiv hπ data H j hj u hu

/-- The same last factor retains its full outgoing quotient in the closing coordinate. -/
theorem arithmeticZeroSecondLastEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (L (m + 1) b).toRingHom =
      (L m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroSecondLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticZeroFirstLastSmoothing_restriction hπ data H j hj u hu m b) _ true
  · exact punctureEquiv_invert_naturality f

/-- The new full closing residual respects the original coefficient quotient. -/
theorem arithmeticZeroSecondClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroSecondClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact symm_naturality f _ _
        (twoBranchCorrectionRebasedPunctureFactor_restriction R π m _ _
          (arithmeticFourthTerminalSmoothing_restriction hπ data H j hj u hu m) _ b)
    · exact arithmeticZeroFirstClosingEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _
      (arithmeticZeroSecondLastEdgeEquiv_restriction hπ data H j hj u hu m b)

/-- The entire relative initial residual retains every coefficient quotient. -/
theorem arithmeticZeroSecondInitialRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroSecondInitialRelativeEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticZeroSecondInitialEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _ (arithmeticInitialBaseEquiv_restriction data H m j hj)

omit m in
/-- The full relative initial error vanishes at layer two. -/
theorem arithmeticZeroSecondInitialRelativeEquiv_second (b : Bool) : D 2 b = AlgEquiv.refl := by
  rw [arithmeticZeroSecondInitialRelativeEquiv, arithmeticZeroSecondInitialEquiv_second]
  ext z : 1
  exact (arithmeticInitialBaseEquiv data H 2 j hj).symm_apply_apply z

end FLT.Mazur.WeierstrassDividedDepth
