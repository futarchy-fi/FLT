/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatAlgebraEqualizer

/-!
# Exact full-boundary equations in coefficient coordinates

Three full ring comparisons and three commuting squares identify the actual
solution sets. The target boundary element is transported literally.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatBoundaryCoordinateEquations
open FlatAlgebraEqualizer
variable {R S A C B A' C' B' : Type*}
  [CommRing R] [CommRing S] [CommRing A] [CommRing C] [CommRing B]
  [CommRing A'] [CommRing C'] [CommRing B']
  [Algebra R S] [Algebra R A] [Algebra R C] [Algebra R B]
  (p q : A →ₐ[R] C) (f : A →ₐ[R] B)
  (ea : S ⊗[R] A ≃+* A') (ec : S ⊗[R] C ≃+* C') (eb : S ⊗[R] B ≃+* B')
  (p' q' : A' →+* C') (f' : A' →+* B')

/-- Full-coordinate transport preserves and reflects existence of a full boundary solution. -/
theorem lift_iff
    (hp : ∀ x, ec (tensorMap S p x) = p' (ea x))
    (hq : ∀ x, ec (tensorMap S q x) = q' (ea x))
    (hf : ∀ x, eb (tensorMap S f x) = f' (ea x)) (t : B) (t' : B')
    (ht : eb (1 ⊗ₜ[R] t) = t') :
    (∃ a : S ⊗[R] A, tensorMap S p a = tensorMap S q a ∧
      tensorMap S f a = 1 ⊗ₜ[R] t) ↔ ∃ a : A', p' a = q' a ∧ f' a = t' := by
  constructor
  · rintro ⟨a, he, hb⟩
    refine ⟨ea a, ?_, ?_⟩
    · rw [← hp, ← hq, he]
    · rw [← hf, hb, ht]
  · rintro ⟨a, he, hb⟩
    refine ⟨ea.symm a, ec.injective ?_, eb.injective ?_⟩
    · rw [hp, hq, ea.apply_symm_apply, he]
    · rw [hf, ea.apply_symm_apply, hb, ht]

end FLT.Mazur.FlatBoundaryCoordinateEquations
