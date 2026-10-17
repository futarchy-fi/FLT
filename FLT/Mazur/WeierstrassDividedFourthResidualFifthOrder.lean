/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthResidualRestriction

/-!
# Fifth-order bounds for all three full fourth residual positions

The original quotient squares and stage-three cancellation give divisibility
of every Laurent coefficient and the entire error. No support is truncated.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "p" => parameter R π m
local notation "J" => Ideal.map (algebraMap Q L) (ideal Q p)
local notation "C" => arithmeticFourthClosingEquiv hπ data H j hj u hu
local notation "I" => arithmeticFourthIncomingEquiv hπ data H j hj u hu
local notation "E" => arithmeticFourthPrecedingEquiv hπ data H j hj u hu

/-- The full closing residual commutes with every nonconsecutive coefficient quotient. -/
theorem arithmeticFourthClosingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (C m b).toRingHom =
      (C k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (C r b).toAlgHom)
    (fun r ↦ arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the actual closing error is divisible by pi to the fifth power. -/
theorem arithmeticFourthClosing_coeff_dvd (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 5 ∣ (C m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (C r b).toAlgHom)
    (fun r ↦ arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticFourthClosingEquiv_fourth hπ data H j hj u hu b)

/-- The entire closing error belongs to the fifth coefficient-ideal power. -/
theorem arithmeticFourthClosing_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    C m b z - z ∈ J ^ 5 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (C r b).toAlgHom)
    (fun r ↦ arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticFourthClosingEquiv_fourth hπ data H j hj u hu b)

/-- The full incoming residual commutes with every nonconsecutive coefficient quotient. -/
theorem arithmeticFourthIncomingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (I m b).toRingHom =
      (I k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (I r b).toAlgHom)
    (fun r ↦ arithmeticFourthIncomingEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the actual incoming error is divisible by pi to the fifth power. -/
theorem arithmeticFourthIncoming_coeff_dvd (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 5 ∣ (I m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (I r b).toAlgHom)
    (fun r ↦ arithmeticFourthIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticFourthIncomingEquiv_fourth hπ data H j hj u hu b)

/-- The entire incoming error belongs to the fifth coefficient-ideal power. -/
theorem arithmeticFourthIncoming_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    I m b z - z ∈ J ^ 5 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (I r b).toAlgHom)
    (fun r ↦ arithmeticFourthIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticFourthIncomingEquiv_fourth hπ data H j hj u hu b)

/-- The full preceding residual commutes with every nonconsecutive coefficient quotient. -/
theorem arithmeticFourthPrecedingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (E m b).toRingHom =
      (E k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFourthPrecedingEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the actual preceding error is divisible by pi to the fifth power. -/
theorem arithmeticFourthPreceding_coeff_dvd (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 5 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFourthPrecedingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticFourthPrecedingEquiv_fourth hπ data H j hj u hu b)

/-- The entire preceding error belongs to the fifth coefficient-ideal power. -/
theorem arithmeticFourthPreceding_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    E m b z - z ∈ J ^ 5 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFourthPrecedingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticFourthPrecedingEquiv_fourth hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
