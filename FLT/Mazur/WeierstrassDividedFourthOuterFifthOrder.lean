/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterRestriction

/-!
# Fifth-order bounds for the simultaneous further retained corrections

The original quotient squares and stage-four cancellation give divisibility
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
local notation "I" => arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu
local notation "E" => arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu

/-- The full incoming residual commutes with every nonconsecutive coefficient quotient. -/
theorem arithmeticFourthOuterIncomingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (I m b).toRingHom =
      (I k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (I r b).toAlgHom)
    (fun r ↦ arithmeticFourthOuterIncomingEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the actual incoming error is divisible by pi to the fifth power. -/
theorem arithmeticFourthOuterIncoming_coeff_dvd (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 5 ∣ (I m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (I r b).toAlgHom)
    (fun r ↦ arithmeticFourthOuterIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthOuterIncomingEquiv_fourth hπ data H j hj u hu b)

/-- The entire incoming error belongs to the fifth coefficient-ideal power. -/
theorem arithmeticFourthOuterIncoming_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    I m b z - z ∈ J ^ 5 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (I r b).toAlgHom)
    (fun r ↦ arithmeticFourthOuterIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthOuterIncomingEquiv_fourth hπ data H j hj u hu b)

/-- The full preceding residual commutes with every nonconsecutive coefficient quotient. -/
theorem arithmeticFourthOuterPrecedingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (E m b).toRingHom =
      (E k b).toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFourthOuterPrecedingEquiv_restriction hπ data H j hj u hu r b) hk

/-- Every coefficient of the actual preceding error is divisible by pi to the fifth power. -/
theorem arithmeticFourthOuterPreceding_coeff_dvd (hm : 4 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 5 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFourthOuterPrecedingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthOuterPrecedingEquiv_fourth hπ data H j hj u hu b)

/-- The entire preceding error belongs to the fifth coefficient-ideal power. -/
theorem arithmeticFourthOuterPreceding_sub_mem (hm : 4 ≤ m) (b : Bool) (z : L) :
    E m b z - z ∈ J ^ 5 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFourthOuterPrecedingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFourthOuterPrecedingEquiv_fourth hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
