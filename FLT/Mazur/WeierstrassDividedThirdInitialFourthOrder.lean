/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdInitialCancellation
public import FLT.Mazur.WeierstrassDividedInitialBaseRestriction
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction

/-!
# Fourth-order initial errors relative to the original full base parameter

The raw residual is not asserted to be identity. Removing its exact original
Mobius/right parameter produces a natural residual with fourth-order error.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "E" => arithmeticThirdInitialEquiv hπ data H j hj u hu
local notation "B" => fun k ↦ arithmeticInitialBaseEquiv data H k j hj

/-- The full raw initial residual preserves every original coefficient restriction. -/
theorem arithmeticThirdInitialEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdInitialEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · apply punctureEquiv_trans_naturality
      · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
          (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b) _ false
      · exact arithmeticSecondPrecedingOpposite_restriction hπ data H m j hj u hu b
    · exact arithmeticInitialBaseEquiv_restriction data H m j hj
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true

/-- Compare the complete initial residual with its actual original base parameter. -/
def arithmeticThirdInitialRelativeEquiv (b : Bool) : L ≃ₐ[Q] L :=
  (E m b).trans (B m).symm

local notation "D" => arithmeticThirdInitialRelativeEquiv hπ data H j hj u hu

omit m in
/-- The relative residual is identity at stage three, with the full base parameter removed. -/
theorem arithmeticThirdInitialRelativeEquiv_third (b : Bool) : D 3 b = AlgEquiv.refl := by
  unfold arithmeticThirdInitialRelativeEquiv
  rw [arithmeticThirdInitialEquiv_third]
  ext z : 1
  exact AlgEquiv.symm_apply_apply (arithmeticInitialBaseEquiv data H 3 j hj) z

/-- The complete relative residual retains the same adjacent coefficient quotient. -/
theorem arithmeticThirdInitialRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdInitialRelativeEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticThirdInitialEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _ (arithmeticInitialBaseEquiv_restriction data H m j hj)

/-- Relative initial errors commute with every nonconsecutive arithmetic quotient. -/
theorem arithmeticThirdInitialRelativeEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (D m b).toRingHom =
      (D k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticThirdInitialRelativeEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the initial relative error is divisible by pi to the fourth power. -/
theorem arithmeticThirdInitialRelative_coeff_dvd (hm : 3 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 4 ∣ (D m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticThirdInitialRelativeEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticThirdInitialRelativeEquiv_third hπ data H j hj u hu b)

/-- The entire relative initial error lies in the fourth coefficient-ideal power. -/
theorem arithmeticThirdInitialRelative_sub_mem (hm : 3 ≤ m) (b : Bool) (z : L) :
    D m b z - z ∈ ((ideal Q (parameter R π m)).map (algebraMap Q L)) ^ 4 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticThirdInitialRelativeEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticThirdInitialRelativeEquiv_third hπ data H j hj u hu b)

/-- The raw initial residual differs from its full original base map only in fourth order. -/
theorem arithmeticThirdInitial_sub_base_mem (hm : 3 ≤ m) (b : Bool) (z : L) :
    E m b z - B m z ∈ ((ideal Q (parameter R π m)).map (algebraMap Q L)) ^ 4 := by
  let J := (ideal Q (parameter R π m)).map (algebraMap Q L)
  have hB : J ^ 4 ≤ Ideal.comap (B m).toRingHom (J ^ 4) := by
    rw [← Ideal.map_pow]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change B m (algebraMap Q L x) ∈ Ideal.map (algebraMap Q L) _
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hx
  have h := hB (arithmeticThirdInitialRelative_sub_mem hπ data H j hj u hu m hm b z)
  change B m ((B m).symm (E m b z) - z) ∈ J ^ 4 at h
  rw [map_sub, AlgEquiv.apply_symm_apply] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
