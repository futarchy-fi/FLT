/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherOppositePuncture
public import FLT.Mazur.WeierstrassDividedSecondJointGeometry
public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction

/-!
# The remaining predecessor puncture and its higher error

The opposite predecessor puncture is identity at stage two. Its full higher
substitution and changed smoothing are retained over the original quotients.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "q" => arithmeticSecondPrecedingIntegralField hπ data H j hj u hu

/-- The remaining predecessor puncture keeps the entire inverse multiplier. -/
def arithmeticSecondPrecedingOpposite (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  correctionPunctureFactor R π m τ (q b) false

omit m in
/-- The predecessor smoothing is unchanged on the second layer only. -/
theorem arithmeticSecondPrecedingSmoothing_second (b : Bool) :
    arithmeticSecondPrecedingSmoothing hπ data H 2 j hj u hu b =
      arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2 :=
  correctionSmoothing_higher_eq R π 2 1 _ (arithmeticSecondSmoothing_annihilated data H) _

omit m in
/-- The predecessor's other full puncture is unchanged on the second layer. -/
theorem arithmeticSecondPrecedingOpposite_second (b : Bool) :
    arithmeticSecondPrecedingOpposite hπ data H 2 j hj u hu b = AlgEquiv.refl :=
  correctionPunctureFactor_higher_opposite R π 2 1 _
    (arithmeticSecondSmoothing_annihilated data H) _

local notation "P" => fun k ↦ arithmeticSecondPrecedingOpposite hπ data H k j hj u hu

/-- The full opposite error preserves the original adjacent arithmetic quotient square. -/
theorem arithmeticSecondPrecedingOpposite_restriction (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (coeffMap (restriction R π m).toRingHom) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ false

/-- The exact predecessor smoothing retains its original coefficient restriction. -/
theorem arithmeticSecondPrecedingSmoothing_restriction (b : Bool) :
    restriction R π m (arithmeticSecondPrecedingSmoothing hπ data H (m + 1) j hj u hu b) =
      arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

local notation "L" => Q[T;T⁻¹]
local notation "p" => parameter R π m
local notation "J" => Ideal.map (algebraMap Q L) (ideal Q p)

/-- Every coefficient of the full remaining predecessor error is divisible by pi cubed. -/
theorem arithmeticSecondPrecedingOpposite_coeff_dvd
    (hm : 2 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    p ^ 3 ∣ (P m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (P r b).toAlgHom)
    (fun r ↦ arithmeticSecondPrecedingOpposite_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondPrecedingOpposite_second hπ data H j hj u hu b)

/-- The full higher predecessor error lies in the third coefficient ideal power. -/
theorem arithmeticSecondPrecedingOpposite_sub_mem (hm : 2 ≤ m) (b : Bool) (z : L) :
    P m b z - z ∈ J ^ 3 := by
  apply laurentSystem_error_sub_mem (fun r ↦ (P r b).toAlgHom)
    (fun r ↦ arithmeticSecondPrecedingOpposite_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondPrecedingOpposite_second hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
