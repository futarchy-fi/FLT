/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Finite presentation after a surjective change of acting ring

If an action factors through a quotient of the coefficient ring, finite
presentation for the old action implies finite presentation for the new one.
This also transports finite presentation along ring isomorphisms.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a surjective scalar map, extending an already factored action changes no module. -/
def surjectiveScalarsTensorEquiv (h : Function.Surjective (algebraMap R S)) :
    S ⊗[R] M ≃ₗ[S] M :=
  LinearEquiv.ofBijective (LinearMap.liftBaseChange S (LinearMap.id : M →ₗ[R] M)) (by
    constructor
    · intro x y hxy
      obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective R M S h x
      obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective R M S h y
      simpa using congrArg (fun z : M ↦ (1 : S) ⊗ₜ[R] z) hxy
    · intro x
      exact ⟨1 ⊗ₜ[R] x, by simp⟩)

/-- Finite presentation survives replacing the acting ring by a quotient. -/
theorem finitePresentation_of_surjective_scalars
    (h : Function.Surjective (algebraMap R S)) [Module.FinitePresentation R M] :
    Module.FinitePresentation S M :=
  Module.FinitePresentation.of_equiv (surjectiveScalarsTensorEquiv (M := M) h)

/-- A ring isomorphism transports finite presentation of the actual ideal. -/
theorem ideal_finitePresentation_map_equiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) [Module.FinitePresentation A I] :
    Module.FinitePresentation B (I.map e.toRingHom) := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let f := Algebra.idealMap B I
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx, hxy⟩ :=
        (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let _ : Module.FinitePresentation A (I.map e.toRingHom) :=
    Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective f hf)
  exact finitePresentation_of_surjective_scalars e.surjective

end FLT.Mazur.FCurve
