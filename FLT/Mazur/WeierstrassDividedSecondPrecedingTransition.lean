/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondPrecedingIncoming
public import FLT.Mazur.WeierstrassDividedSecondJointThirdOrder

/-!
# The remaining predecessor transition as a full arithmetic Laurent system

Conjugation by inversion identifies the actual incoming geometric residual.
Its quotient squares and stage-two identity give a third-order full error.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m

/-- The entire opposite predecessor substitution in the reciprocal incoming coordinate. -/
def arithmeticSecondPrecedingIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (arithmeticSecondPrecedingOpposite hπ data H m j hj u hu b)).trans invert

/-- The algebra formula is exactly the actual full geometric predecessor residual. -/
theorem arithmeticSecondPrecedingIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticSecondPrecedingIncomingEquiv hπ data H m j hj u hu b) =
      arithmeticSecondPrecedingIncomingIso hπ data H m j hj u hu b := by
  simp only [arithmeticSecondPrecedingIncomingEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticSecondPrecedingIncomingIso]
  rfl

omit m in
/-- The whole reciprocal residual is identity at stage two. -/
theorem arithmeticSecondPrecedingIncomingEquiv_second (b : Bool) :
    arithmeticSecondPrecedingIncomingEquiv hπ data H 2 j hj u hu b = AlgEquiv.refl := by
  rw [arithmeticSecondPrecedingIncomingEquiv, arithmeticSecondPrecedingOpposite_second]
  ext z : 1
  exact involutive_invert z

local notation "E" => fun k ↦ arithmeticSecondPrecedingIncomingEquiv hπ data H k j hj u hu
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The full reciprocal residual retains the original adjacent coefficient quotient. -/
theorem arithmeticSecondPrecedingIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toAlgHom.toRingHom =
      (E m b).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondPrecedingIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact arithmeticSecondPrecedingOpposite_restriction hπ data H m j hj u hu b
  · exact punctureEquiv_invert_naturality f

/-- Its full error has cubic coefficient divisibility in the actual edge coordinate. -/
theorem arithmeticSecondPrecedingIncomingEquiv_coeff_dvd (hm : 2 ≤ m)
    (b : Bool) (z : Q[T;T⁻¹]) (d : ℤ) :
    parameter R π m ^ 3 ∣ (E m b z - z).coeff d := by
  apply laurentSystem_error_coeff_dvd (fun r ↦ (E r b).toAlgHom)
    (fun r ↦ arithmeticSecondPrecedingIncomingEquiv_restriction hπ data H r j hj u hu b) hm
  exact congrArg AlgEquiv.toAlgHom
    (arithmeticSecondPrecedingIncomingEquiv_second hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
