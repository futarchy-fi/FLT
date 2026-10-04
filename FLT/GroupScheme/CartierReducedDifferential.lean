/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierLinearCotangent

/-! # The Cartier differential across a square-zero coefficient reduction -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Finite freeness lifts dual coefficients linearly, without an algebra section. -/
theorem exists_linear_character_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (ψ : CartierDual R A →ₐ[R] C) :
    ∃ χ : CartierDual R A →ₗ[R] B, q.toLinearMap.comp χ = ψ.toLinearMap := by
  let : Module.Free R (CartierDual R A) := Module.Free.of_equiv
    (linearEquiv (R := R) (A := A)).symm
  exact Module.projective_lifting_property q.toLinearMap ψ.toLinearMap hq

/-- One linear lift of the original character coefficients; no multiplicativity is asserted. -/
def linearCharacterLift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (ψ : CartierDual R A →ₐ[R] C) : CartierDual R A →ₗ[R] B :=
  (exists_linear_character_lift q hq ψ).choose

/-- The chosen linear coefficients reduce to the specified original character. -/
theorem linearCharacterLift_reduction (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (ψ : CartierDual R A →ₐ[R] C) :
    q.toLinearMap.comp (linearCharacterLift q hq ψ) = ψ.toLinearMap :=
  (exists_linear_character_lift q hq ψ).choose_spec

/-- The original reduced character acts linearly on kernel-valued augmentation tangents. -/
def reducedLogDifferential (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (ψ : CartierDual R A →ₐ[R] C) :
    (Bialgebra.counitAlgHom R A).augmentationTangent (M := RingHom.ker q) →ₗ[R] B :=
  { toFun d := linearTestEvaluation (linearCharacterLift q hq ψ)
      (((RingHom.ker q).subtype.restrictScalars R).comp d.val)
    map_add' d e := by simp [LinearMap.comp_add]
    map_smul' r d := by simp [LinearMap.comp_smul] }

/-- Every linear lift computes the same differential in a square-zero thickening. -/
theorem reducedLogDifferential_eq_lift (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (ψ : CartierDual R A →ₐ[R] C)
    (χ : CartierDual R A →ₗ[R] B) (hχ : q.toLinearMap.comp χ = ψ.toLinearMap)
    (d : (Bialgebra.counitAlgHom R A).augmentationTangent (M := RingHom.ker q)) :
    reducedLogDifferential q hq ψ d =
      linearTestEvaluation χ (((RingHom.ker q).subtype.restrictScalars R).comp d.val) :=
  linearTestEvaluation_lift_independent q hJ _ χ
    ((linearCharacterLift_reduction q hq ψ).trans hχ.symm) _ (fun a ↦ (d.val a).property)

/-- Its value belongs to the actual coefficient kernel. -/
theorem reducedLogDifferential_mem_kernel (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (ψ : CartierDual R A →ₐ[R] C)
    (d : (Bialgebra.counitAlgHom R A).augmentationTangent (M := RingHom.ker q)) :
    reducedLogDifferential q hq ψ d ∈ RingHom.ker q :=
  linearTestEvaluation_mem_kernel q _ _ (fun a ↦ (d.val a).property)

/-- If an algebra lift happens to exist, the differential recovers its actual character value. -/
theorem reducedLogDifferential_character (q : B →ₐ[R] C) (hq : Function.Surjective q)
    (hJ : RingHom.ker q ^ 2 = ⊥) (χ : CartierDual R A →ₐ[R] B)
    (f : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    reducedLogDifferential q hq (q.comp χ)
        (AlgHom.augmentationPointToTangent _ q hJ f) =
      (testCharacter χ (WithConv.toConv f.val) : B) - 1 := by
  rw [reducedLogDifferential_eq_lift q hq hJ _ χ.toLinearMap rfl,
    linearTestEvaluation_algHom, testCharacter_squareZero χ q hJ f]
  rfl

end HopfAlgebra.CartierDual
