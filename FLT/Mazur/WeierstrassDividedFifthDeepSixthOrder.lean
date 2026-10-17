/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepEarlierNodes
public import FLT.Mazur.PolygonArithmeticHigherOppositePuncture
public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction

/-!
# The next opposite compensation after the next earlier fifth factor

Both direct and reciprocal substitutions retain their full original quotient
squares. Their errors vanish at layer five and are divisible by sixth order.
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
local notation "V" => arithmeticFifthDeepEarlierIntegralField hπ data H j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The full direct opposite substitution used by the original initial neighbor. -/
def arithmeticFifthDeepEarlierOppositeEquiv (b : Bool) : L ≃ₐ[Q] L :=
  correctionPunctureFactor R π m τ (V b) false

local notation "O" => arithmeticFifthDeepEarlierOppositeEquiv hπ data H j hj u hu

/-- The full opposite substitution in the reciprocal coordinate of retained adjacent edges. -/
def arithmeticFifthDeepEarlierIncomingEquiv (b : Bool) : L ≃ₐ[Q] L :=
  (invert.trans (O m b)).trans invert

local notation "E" => arithmeticFifthDeepEarlierIncomingEquiv hπ data H j hj u hu

omit m in
/-- The full direct opposite error vanishes on the fifth layer. -/
theorem arithmeticFifthDeepEarlierOppositeEquiv_fifth (b : Bool) : O 5 b = AlgEquiv.refl :=
  correctionPunctureFactor_higher_opposite R π 5 4 _
    (arithmeticTopSmoothing_annihilated data H 5) _

omit m in
/-- The full reciprocal error vanishes on that same layer. -/
theorem arithmeticFifthDeepEarlierIncomingEquiv_fifth (b : Bool) : E 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthDeepEarlierIncomingEquiv
  rw [arithmeticFifthDeepEarlierOppositeEquiv_fifth]
  ext z : 1
  exact involutive_invert z

/-- The direct opposite factor retains every original coefficient quotient. -/
theorem arithmeticFifthDeepEarlierOppositeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (O (m + 1) b).toRingHom =
      (O m b).toRingHom.comp (coeffMap f) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ false

/-- The actual reciprocal residual retains the same full quotient square. -/
theorem arithmeticFifthDeepEarlierIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthDeepEarlierIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact arithmeticFifthDeepEarlierOppositeEquiv_restriction hπ data H j hj u hu m b
  · exact punctureEquiv_invert_naturality f

/-- Every coefficient of the direct error has sixth-order divisibility. -/
theorem arithmeticFifthDeepEarlierOpposite_coeff_dvd (hm : 5 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 6 ∣ (O m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (O r b).toAlgHom)
    (fun r ↦ arithmeticFifthDeepEarlierOppositeEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFifthDeepEarlierOppositeEquiv_fifth hπ data H j hj u hu b)

/-- Every coefficient of the reciprocal incoming error has the same sixth-order bound. -/
theorem arithmeticFifthDeepEarlierIncoming_coeff_dvd (hm : 5 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 6 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticFifthDeepEarlierIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticFifthDeepEarlierIncomingEquiv_fifth hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
