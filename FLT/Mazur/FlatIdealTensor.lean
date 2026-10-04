/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FaithfullyFlatFinitePresentation

/-!
# Tensor extension of an ideal along a flat algebra

The comparison is multiplication after tensoring the actual ideal inclusion.
Its image is the extended ideal; flatness makes it injective. Consequently
finite presentation of an ideal descends from its faithfully flat extension.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Tensor the ideal inclusion and multiply in the target algebra. -/
def idealTensorInclusion (I : Ideal R) : S ⊗[R] I →ₗ[S] S :=
  (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S I.subtype

@[simp]
lemma idealTensorInclusion_tmul (I : Ideal R) (s : S) (x : I) :
    idealTensorInclusion I (s ⊗ₜ[R] x) = s * algebraMap R S x := by
  simp [idealTensorInclusion, Algebra.smul_def, mul_comm]

/-- The image of the tensor comparison is precisely extension of the ideal. -/
lemma idealTensorInclusion_range (I : Ideal R) :
    LinearMap.range (idealTensorInclusion (S := S) I) = I.map (algebraMap R S) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | add x y hx hy => simpa only [map_add] using Ideal.add_mem _ hx hy
    | tmul s x =>
      simpa only [idealTensorInclusion_tmul] using
        Ideal.mul_mem_left _ s (Ideal.mem_map_of_mem (algebraMap R S) x.2)
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact ⟨1 ⊗ₜ[R] ⟨x, hx⟩, by simp⟩

/-- Flatness identifies tensor extension with the actual extended ideal. -/
def flatIdealTensorEquiv [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  (LinearEquiv.ofInjective (idealTensorInclusion I) (by
    exact (AlgebraTensorModule.rid R S S).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.subtype_injective))).trans
    (LinearEquiv.ofEq _ _ (idealTensorInclusion_range I))

@[simp]
lemma flatIdealTensorEquiv_val [Module.Flat R S] (I : Ideal R) (x : S ⊗[R] I) :
    (flatIdealTensorEquiv I x).val = idealTensorInclusion I x := rfl

/-- Finite presentation descends for the extended ideal, without a chosen generator. -/
theorem ideal_finitePresentation_of_faithfullyFlat [Module.FaithfullyFlat R S]
    (I : Ideal R) [Module.FinitePresentation S (I.map (algebraMap R S))] :
    Module.FinitePresentation R I := by
  let : Module.FinitePresentation S (S ⊗[R] I) :=
    Module.FinitePresentation.of_equiv (flatIdealTensorEquiv I).symm
  exact finitePresentation_of_faithfullyFlat (S := S)

end FLT.Mazur.FCurve
