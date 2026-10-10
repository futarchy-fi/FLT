/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousLocalizationRetraction
public import FLT.Mazur.FlatHomogeneousLocalizationBaseChange

/-!
# Arbitrary base change of homogeneous localization

The linear degree-zero retraction survives every scalar extension. Thus the
homogeneous-localization comparison is injective without flatness, and the
existing homogeneous fraction expansion makes it an equivalence.
-/

@[expose] public noncomputable section

open HomogeneousLocalization
open scoped TensorProduct FLT.Mazur.HomogeneousLocalizationScalars

universe u

namespace FLT.Mazur.HomogeneousLocalizationArbitraryBaseChange

open GradedProjBaseChangeMap HomogeneousLocalizationBaseChange
  FlatHomogeneousLocalizationBaseChange HomogeneousLocalizationRetraction

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)

/-- The original linear retraction still retracts the inclusion after arbitrary scalar extension. -/
theorem tensorProjection_val (x : B ⊗[R] Away 𝒜 f) :
    (linearProjection 𝒜 hf).lTensor B (tensorVal 𝒜 f x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul b x =>
    change (linearProjection 𝒜 hf).lTensor B (b ⊗ₜ[R] x.val) = b ⊗ₜ[R] x
    rw [LinearMap.lTensor_tmul, linearProjection_val]
  | add x y hx hy => simp only [map_add, hx, hy]

include hf in
/-- Homogeneous fractions embed after every scalar extension because their inclusion splits. -/
theorem tensorVal_injective : Function.Injective (tensorVal (B := B) 𝒜 f) :=
  (show Function.LeftInverse ((linearProjection 𝒜 hf).lTensor B) (tensorVal 𝒜 f) from
    tensorProjection_val 𝒜 hf).injective

include hf in
/-- The original homogeneous-localization comparison is injective without flatness. -/
theorem comparison_injective : Function.Injective (comparison (B := B) 𝒜 f) := by
  intro x y he
  apply tensorVal_injective 𝒜 hf
  apply (ordinaryEquiv 𝒜 f).injective
  rw [← comparison_val, ← comparison_val, he]

/-- Every scalar extension commutes with degree-zero localization at a homogeneous element. -/
def equiv : B ⊗[R] Away 𝒜 f ≃ₐ[B]
    Away (baseGrade (B := B) 𝒜) (inclusion 𝒜 f) :=
  AlgEquiv.ofBijective (comparison 𝒜 f)
    ⟨comparison_injective 𝒜 hf, comparison_surjective 𝒜 f hf⟩

end FLT.Mazur.HomogeneousLocalizationArbitraryBaseChange
