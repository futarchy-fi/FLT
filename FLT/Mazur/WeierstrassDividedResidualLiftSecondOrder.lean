/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualLiftRestriction
public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction

/-!
# Second-order errors of the actual corrected arithmetic transitions

The full closing residual and the separately affected incoming transitions
reduce to identity at order one. Their original quotient squares force every
error coefficient to be divisible by pi squared at every higher stage.
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
local notation "E" => fun k ↦ arithmeticResidualLiftClosingEquiv hπ data H k j hj u hu
local notation "K" => fun k ↦ arithmeticResidualLiftEdgeEquiv hπ data H k j hj u hu

/-- Both complete corrected closing residuals preserve every nonconsecutive quotient. -/
theorem arithmeticResidualLiftClosingEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (E m b).toAlgHom.toRingHom =
      (E k b).toAlgHom.toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticResidualLiftClosingEquiv_restriction hπ data H r j hj u hu b) hk

/-- Both full retained edge substitutions preserve every nonconsecutive quotient. -/
theorem arithmeticResidualLiftEdgeEquiv_restrictionLE {k : ℕ} (hk : k ≤ m) (b a : Bool) :
    (coeffMap (restrictionLE R π hk).toRingHom).comp (K m b a).toAlgHom.toRingHom =
      (K k b a).toAlgHom.toRingHom.comp (coeffMap (restrictionLE R π hk).toRingHom) :=
  laurentSystem_restrictionLE (fun r ↦ (K r b a).toAlgHom)
    (fun r ↦ arithmeticResidualLiftEdgeEquiv_restriction hπ data H r j hj u hu b a) hk

/-- Every coefficient of the actual full closing error is divisible by pi squared. -/
theorem arithmeticResidualLiftClosing_coeff_dvd (hm : 1 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 2 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticResidualLiftClosingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticResidualLiftClosingEquiv_first hπ data H j hj u hu b)

/-- The entire closing error has one finite Laurent quotient by pi squared. -/
theorem arithmeticResidualLiftClosing_dvd (hm : 1 ≤ m) (b : Bool) (z : L) :
    C (p ^ 2) ∣ E m b z - z :=
  LaurentCoefficientDivisibility.C_dvd_of_coeff _ _
    (arithmeticResidualLiftClosing_coeff_dvd hπ data H m j hj u hu hm b z)

/-- The actual complete residual has second-order error on every Laurent input. -/
theorem arithmeticResidualLiftClosing_sub_mem (hm : 1 ≤ m) (b : Bool) (z : L) :
    E m b z - z ∈ J ^ 2 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticResidualLiftClosingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticResidualLiftClosingEquiv_first hπ data H j hj u hu b)

/-- The full corrected closing error raises every coefficient filtration by two. -/
theorem arithmeticResidualLiftClosing_error_mem_power (hm : 1 ≤ m) (b : Bool)
    (r : ℕ) (z : L) (hz : z ∈ J ^ r) : E m b z - z ∈ J ^ (r + 2) :=
  NilpotentAlgebraHigherOrderError.error_mem_power (R := Q) (A := L)
    (ideal Q p) 2 (E m b).toAlgHom
    (arithmeticResidualLiftClosing_sub_mem hπ data H m j hj u hu hm b) r z hz

/-- The separately affected incoming transition also has full second-order coefficient error. -/
theorem arithmeticResidualLiftIncoming_coeff_dvd (hm : 1 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 2 ∣ (K m b false z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (K r b false).toAlgHom)
    (fun r ↦ arithmeticResidualLiftEdgeEquiv_restriction hπ data H r j hj u hu b false) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticResidualLiftEdgeEquiv_incoming_first hπ data H j hj u hu b)

/-- Incoming errors retain the entire Laurent polynomial inside the second ideal power. -/
theorem arithmeticResidualLiftIncoming_sub_mem (hm : 1 ≤ m) (b : Bool) (z : L) :
    K m b false z - z ∈ J ^ 2 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (K r b false).toAlgHom)
    (fun r ↦ arithmeticResidualLiftEdgeEquiv_restriction hπ data H r j hj u hu b false) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticResidualLiftEdgeEquiv_incoming_first hπ data H j hj u hu b)

/-- The complete incoming error raises every coefficient filtration by two as well. -/
theorem arithmeticResidualLiftIncoming_error_mem_power (hm : 1 ≤ m) (b : Bool)
    (r : ℕ) (z : L) (hz : z ∈ J ^ r) : K m b false z - z ∈ J ^ (r + 2) :=
  NilpotentAlgebraHigherOrderError.error_mem_power (R := Q) (A := L)
    (ideal Q p) 2 (K m b false).toAlgHom
    (arithmeticResidualLiftIncoming_sub_mem hπ data H m j hj u hu hm b) r z hz

/-- Inverting the complete closing residual preserves its second-order error. -/
theorem arithmeticResidualLiftClosing_symm_sub_mem (hm : 1 ≤ m) (b : Bool) (z : L) :
    (E m b).symm z - z ∈ J ^ 2 :=
  NilpotentAlgebraHigherOrderError.symm_sub_mem (R := Q) (A := L) (ideal Q p) 2 (E m b)
    (arithmeticResidualLiftClosing_sub_mem hπ data H m j hj u hu hm b) z

/-- The full inverse incoming transition retains the same second-order error bound. -/
theorem arithmeticResidualLiftIncoming_symm_sub_mem (hm : 1 ≤ m) (b : Bool) (z : L) :
    (K m b false).symm z - z ∈ J ^ 2 :=
  NilpotentAlgebraHigherOrderError.symm_sub_mem (R := Q) (A := L) (ideal Q p) 2 (K m b false)
    (arithmeticResidualLiftIncoming_sub_mem hπ data H m j hj u hu hm b) z

end FLT.Mazur.WeierstrassDividedDepth
