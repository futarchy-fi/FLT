/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowRestriction
public import FLT.Mazur.WeierstrassDividedInitialBaseRestriction
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction

/-!
# Fifth-order initial errors relative to the original full base parameter

The raw residual is not asserted to be identity. Removing its exact original
Mobius/right parameter produces a natural residual with fifth-order error.
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
local notation "E" => arithmeticFourthShallowEquiv hπ data H j hj u hu
local notation "B" => fun k ↦ arithmeticInitialBaseEquiv data H k j hj

/-- Compare the complete initial residual with its actual original base parameter. -/
def arithmeticFourthShallowRelativeEquiv (b : Bool) : L ≃ₐ[Q] L :=
  (E m b).trans (B m).symm

local notation "D" => arithmeticFourthShallowRelativeEquiv hπ data H j hj u hu

omit m in
/-- The relative residual is identity at stage four, with the full base parameter removed. -/
theorem arithmeticFourthShallowRelativeEquiv_fourth (b : Bool) : D 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthShallowRelativeEquiv
  rw [arithmeticFourthShallowEquiv_fourth]
  ext z : 1
  exact AlgEquiv.symm_apply_apply (arithmeticInitialBaseEquiv data H 4 j hj) z

/-- The complete relative residual retains the same adjacent coefficient quotient. -/
theorem arithmeticFourthShallowRelativeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toRingHom =
      (D m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthShallowRelativeEquiv
  apply punctureEquiv_trans_naturality
  · exact arithmeticFourthShallowEquiv_restriction hπ data H j hj u hu m b
  · exact symm_naturality f _ _ (arithmeticInitialBaseEquiv_restriction data H m j hj)

/-- Relative initial errors commute with every nonconsecutive arithmetic quotient. -/
theorem arithmeticFourthShallowRelativeEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (D m b).toRingHom =
      (D k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticFourthShallowRelativeEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the initial relative error is divisible by pi to the fifth power. -/
theorem arithmeticFourthShallowRelative_coeff_dvd (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 5 ∣ (D m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticFourthShallowRelativeEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthShallowRelativeEquiv_fourth hπ data H j hj u hu b)

/-- The entire relative initial error lies in the fifth coefficient-ideal power. -/
theorem arithmeticFourthShallowRelative_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    D m b z - z ∈ ((ideal Q (parameter R π m)).map (algebraMap Q L)) ^ 5 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (D r b).toAlgHom)
    (fun r ↦ arithmeticFourthShallowRelativeEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthShallowRelativeEquiv_fourth hπ data H j hj u hu b)

/-- The raw initial residual differs from its full original base map only in fifth order. -/
theorem arithmeticFourthShallow_sub_base_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    E m b z - B m z ∈ ((ideal Q (parameter R π m)).map (algebraMap Q L)) ^ 5 := by
  let J := (ideal Q (parameter R π m)).map (algebraMap Q L)
  have hB : J ^ 5 ≤ Ideal.comap (B m).toRingHom (J ^ 5) := by
    rw [← Ideal.map_pow]
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change B m (algebraMap Q L x) ∈ Ideal.map (algebraMap Q L) _
    rw [AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hx
  have h := hB (arithmeticFourthShallowRelative_sub_mem hπ data H j hj u hu m hm b z)
  change B m ((B m).symm (E m b z) - z) ∈ J ^ 5 at h
  rw [map_sub, AlgEquiv.apply_symm_apply] at h
  exact h

/-- Every coefficient of the simultaneously corrected incoming error has fifth-order bound. -/
theorem arithmeticFourthShallowNeighborIncoming_coeff_dvd
    (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 5 ∣
      (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd
    (fun r ↦ (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu r b).toAlgHom)
    (fun r ↦ arithmeticFourthShallowNeighborIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthShallowNeighborIncomingEquiv_fourth hπ data H j hj u hu b)

/-- The entire neighboring incoming error lies in the fifth coefficient-ideal power. -/
theorem arithmeticFourthShallowNeighborIncoming_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu m b z - z ∈
      ((ideal Q (parameter R π m)).map (algebraMap Q L)) ^ 5 := by
  apply laurentSystem_error_sub_mem
    (fun r ↦ (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu r b).toAlgHom)
    (fun r ↦ arithmeticFourthShallowNeighborIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthShallowNeighborIncomingEquiv_fourth hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
