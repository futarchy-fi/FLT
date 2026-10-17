/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierIncoming
public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction

/-!
# Fourth-order errors on the further incoming edge of the third atlas

The direct opposite parameter is used at the original initial neighbor;
the reciprocal form is used at an earlier retained neighbor. Both full maps
preserve the original quotient and have fourth-order error.
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
local notation "V" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The full direct opposite substitution used by the original initial neighbor. -/
def arithmeticThirdEarlierOppositeEquiv (b : Bool) : L ≃ₐ[Q] L :=
  correctionPunctureFactor R π m τ (V b) false

local notation "O" => arithmeticThirdEarlierOppositeEquiv hπ data H j hj u hu

/-- The full opposite substitution in the reciprocal coordinate of retained adjacent edges. -/
def arithmeticThirdEarlierIncomingEquiv (b : Bool) : L ≃ₐ[Q] L :=
  (invert.trans (O m b)).trans invert

local notation "E" => arithmeticThirdEarlierIncomingEquiv hπ data H j hj u hu

/-- The reciprocal algebra map is exactly the already installed further incoming substitution. -/
theorem arithmeticThirdEarlierIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (E m b) = arithmeticThirdEarlierIncomingIso hπ data H m j hj u hu b := by
  simp only [arithmeticThirdEarlierIncomingEquiv, arithmeticThirdEarlierOppositeEquiv,
    punctureSpecIso_trans, punctureSpecIso_invert, arithmeticThirdEarlierIncomingIso]
  rfl

omit m in
/-- The full direct opposite error vanishes on the third layer. -/
theorem arithmeticThirdEarlierOppositeEquiv_third (b : Bool) : O 3 b = AlgEquiv.refl :=
  arithmeticThirdEarlierPuncture_opposite_third hπ data H j hj u hu b

omit m in
/-- The full reciprocal error vanishes on that same layer. -/
theorem arithmeticThirdEarlierIncomingEquiv_third (b : Bool) : E 3 b = AlgEquiv.refl := by
  unfold arithmeticThirdEarlierIncomingEquiv
  rw [arithmeticThirdEarlierOppositeEquiv_third]
  ext z : 1
  exact involutive_invert z

/-- The direct opposite factor retains every original coefficient quotient. -/
theorem arithmeticThirdEarlierOppositeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (O (m + 1) b).toRingHom =
      (O m b).toRingHom.comp (coeffMap f) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ false

/-- The actual reciprocal residual retains the same full quotient square. -/
theorem arithmeticThirdEarlierIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdEarlierIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact arithmeticThirdEarlierOppositeEquiv_restriction hπ data H j hj u hu m b
  · exact punctureEquiv_invert_naturality f

/-- Every coefficient of the direct error has fourth-order divisibility. -/
theorem arithmeticThirdEarlierOpposite_coeff_dvd (hm : 3 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 4 ∣ (O m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (O r b).toAlgHom)
    (fun r ↦ arithmeticThirdEarlierOppositeEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticThirdEarlierOppositeEquiv_third hπ data H j hj u hu b)

/-- Every coefficient of the reciprocal incoming error has the same fourth-order bound. -/
theorem arithmeticThirdEarlierIncoming_coeff_dvd (hm : 3 ≤ m) (b : Bool) (z : L) (d : ℤ) :
    parameter R π m ^ 4 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticThirdEarlierIncomingEquiv_restriction hπ data H j hj u hu r b) hm
  exact congrArg AlgEquiv.toAlgHom (arithmeticThirdEarlierIncomingEquiv_third hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
