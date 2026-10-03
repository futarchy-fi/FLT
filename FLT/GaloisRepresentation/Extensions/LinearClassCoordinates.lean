/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.LinearCoefficientMap

/-!
# Linear finite-basis comparison for continuous classes

The coordinate comparison is linear over the smaller field, and is proved
bijective on the explicit continuous quotient. This supplies a finite-basis
model of coefficient extension without a derived-cohomology API.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

variable {F k G ι : Type*} [Field F] [Field k] [Algebra F k]
    [Group G] [TopologicalSpace G] [Fintype ι]
    (χ : G →* Fˣ) (b : Module.Basis ι F k)

/-- One coefficient coordinate as a linear map. -/
noncomputable def characterCoordinateMap (i : ι) :
    CharacterModule χ k →ₗ[F] CharacterModule χ F :=
  (LinearMap.proj i).comp (characterBasisCoordinates χ b).toLinearMap

omit [TopologicalSpace G] in
/-- A coefficient coordinate commutes with the character action. -/
theorem characterCoordinateMap_equivariant (i : ι) (g : G) (x : CharacterModule χ k) :
    characterCoordinateMap χ b i (g • x) = g • characterCoordinateMap χ b i x :=
  congrFun (characterBasisCoordinates_equivariant χ b g x) i

/-- The linear coordinate map on continuous classes. -/
noncomputable def linearCharacterCoordinates :
    LinearContinuousClass F G (CharacterModule χ k) →ₗ[F]
      (ι → LinearContinuousClass F G (CharacterModule χ F)) :=
  LinearMap.pi fun i ↦ linearCoefficientClass (characterCoordinateMap χ b i)
    (characterCoordinateMap_equivariant χ b i)

/-- The linear map is exactly the previously proved comparison on splitting classes. -/
theorem linearCharacterCoordinates_spec (x : LinearContinuousClass F G (CharacterModule χ k))
    (i : ι) :
    linearClassEquiv (linearCharacterCoordinates χ b x i) =
      characterClassCoordinates χ b (linearClassEquiv x) i := by
  induction x using Quotient.inductionOn with | h c => rfl

/-- The linear comparison is injective because splitting is detected coordinatewise. -/
theorem linearCharacterCoordinates_injective :
    Function.Injective (linearCharacterCoordinates χ b) := by
  intro x y h
  apply linearClassEquiv.injective
  apply (characterClassCoordinates χ b).injective
  funext i
  rw [← linearCharacterCoordinates_spec, ← linearCharacterCoordinates_spec, h]

/-- Representatives of arbitrary coordinate classes reconstruct an extended class. -/
theorem linearCharacterCoordinates_surjective :
    Function.Surjective (linearCharacterCoordinates χ b) := by
  intro y
  refine ⟨linearClassEquiv.symm ((characterClassCoordinates χ b).symm
    (fun i ↦ linearClassEquiv (y i))), ?_⟩
  funext i
  apply linearClassEquiv.injective
  rw [linearCharacterCoordinates_spec, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Continuous classes of an extended line are the prime classes in a finite basis. -/
noncomputable def linearCharacterCoordinatesEquiv :
    LinearContinuousClass F G (CharacterModule χ k) ≃ₗ[F]
      (ι → LinearContinuousClass F G (CharacterModule χ F)) :=
  LinearEquiv.ofBijective (linearCharacterCoordinates χ b)
    ⟨linearCharacterCoordinates_injective χ b, linearCharacterCoordinates_surjective χ b⟩

end GaloisRepresentation.Extensions
