/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointRestriction
public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction

/-!
# Third-order bounds for simultaneous second residuals

The exact incoming and closing formulas are identity at stage two. Their
original quotient squares force full errors into the third coefficient power.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "p" => parameter R π m
local notation "J" => Ideal.map (algebraMap Q L) (ideal Q p)
local notation "E" => fun k ↦ arithmeticSecondJointClosingEquiv hπ data H k j hj u hu
local notation "K" => fun k ↦ arithmeticSecondJointIncomingEquiv hπ data H k j hj u hu

/-- Both complete corrected closing residuals preserve every nonconsecutive quotient. -/
theorem arithmeticSecondJointClosingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (E m b).toAlgHom.toRingHom =
      (E k b).toAlgHom.toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticSecondJointClosingEquiv_restriction hπ data H r j hj u hu b) hk

/-- Both full retained edge substitutions preserve every nonconsecutive quotient. -/
theorem arithmeticSecondJointIncomingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (K m b).toAlgHom.toRingHom =
      (K k b).toAlgHom.toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (K r b).toAlgHom)
    (fun r ↦ arithmeticSecondJointIncomingEquiv_restriction hπ data H r j hj u hu b) hk

/-- Every coefficient of the actual full closing error is divisible by pi cubed. -/
theorem arithmeticSecondJointClosing_coeff_dvd (hm : 2 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 3 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticSecondJointClosingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondJointClosingEquiv_second hπ data H j hj u hu b)

/-- The entire closing error has one finite Laurent quotient by pi cubed. -/
theorem arithmeticSecondJointClosing_dvd (hm : 2 ≤ m) (b : Bool) (z : L) :
    C (p ^ 3) ∣ E m b z - z :=
  LaurentCoefficientDivisibility.C_dvd_of_coeff _ _
    (arithmeticSecondJointClosing_coeff_dvd hπ data H m j hj u hu hm b z)

/-- The actual complete residual has third-order error on every Laurent input. -/
theorem arithmeticSecondJointClosing_sub_mem (hm : 2 ≤ m) (b : Bool) (z : L) :
    E m b z - z ∈ J ^ 3 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticSecondJointClosingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondJointClosingEquiv_second hπ data H j hj u hu b)

/-- The full corrected closing error raises every coefficient filtration by three. -/
theorem arithmeticSecondJointClosing_error_mem_power (hm : 2 ≤ m) (b : Bool)
    (r : ℕ) (z : L) (hz : z ∈ J ^ r) : E m b z - z ∈ J ^ (r + 3) :=
  NilpotentAlgebraHigherOrderError.error_mem_power (R := Q) (A := L)
    (ideal Q p) 3 (E m b).toAlgHom
    (arithmeticSecondJointClosing_sub_mem hπ data H m j hj u hu hm b) r z hz

/-- The separately affected incoming transition also has full third-order coefficient error. -/
theorem arithmeticSecondJointIncoming_coeff_dvd (hm : 2 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 3 ∣ (K m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (K r b).toAlgHom)
    (fun r ↦ arithmeticSecondJointIncomingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondJointIncomingEquiv_second hπ data H j hj u hu b)

/-- Incoming errors retain the entire Laurent polynomial inside the third ideal power. -/
theorem arithmeticSecondJointIncoming_sub_mem (hm : 2 ≤ m) (b : Bool) (z : L) :
    K m b z - z ∈ J ^ 3 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (K r b).toAlgHom)
    (fun r ↦ arithmeticSecondJointIncomingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondJointIncomingEquiv_second hπ data H j hj u hu b)

/-- The complete incoming error raises every coefficient filtration by three as well. -/
theorem arithmeticSecondJointIncoming_error_mem_power (hm : 2 ≤ m) (b : Bool)
    (r : ℕ) (z : L) (hz : z ∈ J ^ r) : K m b z - z ∈ J ^ (r + 3) :=
  NilpotentAlgebraHigherOrderError.error_mem_power (R := Q) (A := L)
    (ideal Q p) 3 (K m b).toAlgHom
    (arithmeticSecondJointIncoming_sub_mem hπ data H m j hj u hu hm b) r z hz

/-- Inverting the complete closing residual preserves its third-order error. -/
theorem arithmeticSecondJointClosing_symm_sub_mem (hm : 2 ≤ m) (b : Bool) (z : L) :
    (E m b).symm z - z ∈ J ^ 3 :=
  NilpotentAlgebraHigherOrderError.symm_sub_mem (R := Q) (A := L) (ideal Q p) 3 (E m b)
    (arithmeticSecondJointClosing_sub_mem hπ data H m j hj u hu hm b) z

/-- The full inverse incoming transition retains the same third-order error bound. -/
theorem arithmeticSecondJointIncoming_symm_sub_mem (hm : 2 ≤ m) (b : Bool) (z : L) :
    (K m b).symm z - z ∈ J ^ 3 :=
  NilpotentAlgebraHigherOrderError.symm_sub_mem (R := Q) (A := L) (ideal Q p) 3 (K m b)
    (arithmeticSecondJointIncoming_sub_mem hπ data H m j hj u hu hm b) z

end FLT.Mazur.WeierstrassDividedDepth
