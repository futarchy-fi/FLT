/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.HardlyRamifiedArithmeticQuotient

/-!
# The upper character at two on the arithmetic quotient

For every specialization of the actual quotient, the determinant and the fixed
quadratic lower character force the upper character. The coordinate projection
is an equivariant surjection; no new filtration hypothesis is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GaloisRepresentation
namespace Deformation
open ProartinianCat
variable (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
variable {p : ℕ} [Fact p.Prime] (hp : Odd p)
  [Algebra ℤ_[p] (residueField (𝓞 := O))] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O (residueField (𝓞 := O))]
  {V : Type} [AddCommGroup V] [Module (residueField (𝓞 := O)) V]
  [Module.Finite (residueField (𝓞 := O)) V] [Module.Free (residueField (𝓞 := O)) V]
  (hdim : Module.rank (residueField (𝓞 := O)) V = 2)
  (ρ : GaloisRep ℚ (residueField (𝓞 := O)) V) (hρ : IsHardlyRamified hp hdim ρ)
  (A : ProartinianCat O) (f : hardlyArithmeticObject O hp hdim ρ hρ ⟶ A)

/-- Every specialization has the upper character required by the fixed determinant. -/
theorem hardlyArithmetic_two_upper (g : Field.absoluteGaloisGroup ℚ_[2]) :
    (hardlyArithmeticEquiv O hp hdim ρ hρ A f).val.val
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g) 0 0 =
      algebraMap O A (hardlyCyclotomicValue (p := p) O
        (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)) *
      algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) := by
  let τ := hardlyArithmeticEquiv O hp hdim ρ hρ A f
  let s := Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g
  let c : A := algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O)
  have h10 : τ.val.val s 1 0 = 0 := by simpa using τ.property.2.2 g 0
  have h11 : τ.val.val s 1 1 = c := by simpa [c] using τ.property.2.2 g 1
  have hsq : c * c = 1 := by
    have ho : (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) ^ 2 = 1 :=
      congrArg Units.val (quadraticCharacterLift_sq
        (hardlyTwoCharacter O hp hdim ρ hρ) (hardlyTwoCharacter_sq O hp hdim ρ hρ) O g)
    simpa [c, ← map_mul, ← pow_two] using congrArg (algebraMap O A) ho
  have hd := τ.property.1 s
  rw [Matrix.det_fin_two, h10, h11, mul_zero, sub_zero] at hd
  change τ.val.val s 0 0 = _ * c
  calc
    τ.val.val s 0 0 = τ.val.val s 0 0 * (c * c) := by rw [hsq, mul_one]
    _ = (τ.val.val s 0 0 * c) * c := (mul_assoc _ _ _).symm
    _ = _ := congrArg (fun x ↦ x * c) hd

/-- The second coordinate remains equivariant for the specified quotient character. -/
theorem hardlyArithmetic_two_projection (g : Field.absoluteGaloisGroup ℚ_[2])
    (x : Fin 2 → A) :
    (((hardlyArithmeticEquiv O hp hdim ρ hρ A f).val.val
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)).val.mulVec x) 1 =
        algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) * x 1 := by
  let τ := hardlyArithmeticEquiv O hp hdim ρ hρ A f
  have h0 := τ.property.2.2 g 0
  have h1 := τ.property.2.2 g 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change τ.val.val _ 1 0 * x 0 + τ.val.val _ 1 1 * x 1 = _
  simp only [h0, h1, Fin.zero_eq_one_iff, Nat.reduceEqDiff, ite_false, ite_true,
    zero_mul, zero_add]

/-- The prescribed quotient is an actual surjective linear map of the specialized action. -/
theorem hardlyArithmetic_two_quotient :
    ∃ π : (Fin 2 → A) →ₗ[A] A, Function.Surjective π ∧
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (x : Fin 2 → A),
        π (((hardlyArithmeticEquiv O hp hdim ρ hρ A f).val.val
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[2]) g)).val.mulVec x) =
            algebraMap O A (hardlyTwoIntegralCharacter O hp hdim ρ hρ g : O) * π x := by
  refine ⟨LinearMap.proj 1, fun a ↦ ⟨fun _ ↦ a, rfl⟩, ?_⟩
  exact hardlyArithmetic_two_projection O hp hdim ρ hρ A f

end Deformation
