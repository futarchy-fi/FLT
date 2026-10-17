/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstRestriction

/-!
# Full relative residuals after the first depth-zero correction

Both initial and closing residuals use the same installed node inputs. Their
complete coefficient quotients and first-layer identities supply the next fields.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthClosingEquiv arithmeticZeroFirstLastEdgeEquiv
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "L" => arithmeticZeroFirstLastEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticZeroFirstClosingEquiv hπ data H j hj u hu

/-- Remove only the entire original initial base to measure the new relative error. -/
def arithmeticZeroFirstInitialRelativeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (arithmeticZeroFirstInitialEquiv hπ data H j hj u hu m b).trans
    (arithmeticInitialBaseEquiv data H m j hj).symm

local notation "D" => arithmeticZeroFirstInitialRelativeEquiv hπ data H j hj u hu

/-- The same last factor retains its full outgoing quotient in the closing coordinate. -/
theorem arithmeticZeroFirstLastEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (L (m + 1) b).toRingHom =
      (L m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroFirstLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true
  · exact punctureEquiv_invert_naturality f

/-- The new full closing residual respects the original coefficient quotient. -/
theorem arithmeticZeroFirstClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroFirstClosingEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _
      (arithmeticZeroFirstLastEdgeEquiv_restriction hπ data H j hj u hu m b)

/-- The entire relative initial residual retains every coefficient quotient. -/
theorem arithmeticZeroFirstInitialRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroFirstInitialRelativeEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticZeroFirstInitialEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _ (arithmeticInitialBaseEquiv_restriction data H m j hj)

omit m in
/-- The full relative initial error vanishes at layer one. -/
theorem arithmeticZeroFirstInitialRelativeEquiv_first (b : Bool) : D 1 b = AlgEquiv.refl := by
  rw [arithmeticZeroFirstInitialRelativeEquiv, arithmeticZeroFirstInitialEquiv_first]
  ext z : 1
  exact (arithmeticInitialBaseEquiv data H 1 j hj).symm_apply_apply z

end FLT.Mazur.WeierstrassDividedDepth
