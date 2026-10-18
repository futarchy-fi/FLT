/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthRestriction

/-!
# Full relative residuals after the fifth depth-zero correction

Both initial and closing residuals use the same installed node inputs. Their
complete coefficient quotients and fifth-layer identities supply the next fields.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroFourthClosingEquiv arithmeticZeroFifthLastEdgeEquiv
  arithmeticZeroFifthInitialEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "L" => arithmeticZeroFifthLastEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticZeroFifthClosingEquiv hπ data H j hj u hu

/-- Remove only the entire original initial base to measure the new relative error. -/
def arithmeticZeroFifthInitialRelativeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticZeroFifthInitialEquiv hπ data H j hj u hu m b).trans
    (arithmeticInitialBaseEquiv data H m j hj).symm

local notation "D" => arithmeticZeroFifthInitialRelativeEquiv hπ data H j hj u hu

/-- The same last factor retains its full outgoing quotient in the closing coordinate. -/
theorem arithmeticZeroFifthLastEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (L (m + 1) b).toRingHom =
      (L m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroFifthLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticZeroFourthLastSmoothing_restriction hπ data H j hj u hu m b) _ true
  · exact punctureEquiv_invert_naturality f

/-- The new full closing residual respects the original coefficient quotient. -/
theorem arithmeticZeroFifthClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroFifthClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact symm_naturality f _ _
        (twoBranchCorrectionRebasedPunctureFactor_restriction R π m _ _
          (arithmeticZeroFourthTerminalSmoothing_restriction hπ data H j hj u hu m) _ b)
    · exact arithmeticZeroFourthClosingEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _
      (arithmeticZeroFifthLastEdgeEquiv_restriction hπ data H j hj u hu m b)

/-- The entire relative initial residual retains every coefficient quotient. -/
theorem arithmeticZeroFifthInitialRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroFifthInitialRelativeEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticZeroFifthInitialEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _ (arithmeticInitialBaseEquiv_restriction data H m j hj)

omit m in
/-- The full relative initial error vanishes at layer five. -/
theorem arithmeticZeroFifthInitialRelativeEquiv_fifth (b : Bool) : D 5 b = AlgEquiv.refl := by
  rw [arithmeticZeroFifthInitialRelativeEquiv, arithmeticZeroFifthInitialEquiv_fifth]
  ext z : 1
  exact (arithmeticInitialBaseEquiv data H 5 j hj).symm_apply_apply z

end FLT.Mazur.WeierstrassDividedDepth
