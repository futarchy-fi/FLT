/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionBaseChange

/-!
# Comparing the affine obstruction with an actual base-change algebra

An algebra equivalence transports the ideal tensor test and its transition.
The commutativity condition identifies the actual old algebra map, so vanishing
in the displayed tensor algebra follows from vanishing in the actual stage.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineObstructionEquiv
variable {R A S B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing B] [Algebra S B]
  (e : S ⊗[R] A ≃ₐ[S] B)

/-- Compare the actual ideal tensor modules over the new base. -/
def comparison (J : Ideal S) : (S ⊗[R] A) ⊗[S] J ≃ₗ[S] B ⊗[S] J :=
  e.toLinearEquiv.rTensor J

/-- This comparison commutes with multiplication into the actual algebra. -/
theorem inclusion_comparison (J : Ideal S) (z : (S ⊗[R] A) ⊗[S] J) :
    FCurve.idealTensorInclusion J (comparison e J z) =
      e (FCurve.idealTensorInclusion J z) := by
  induction z with
  | tmul a i =>
    simp only [comparison, LinearEquiv.rTensor_tmul, FCurve.idealTensorInclusion_tmul]
    change e a * algebraMap S B i.val = e (a * algebraMap S (S ⊗[R] A) i.val)
    rw [map_mul, e.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (s : A →+* B)
  (hs : s.comp (algebraMap R A) = (algebraMap S B).comp (algebraMap R S))
  (he : ∀ a, e (AffineObstructionBaseChange.rightMap S a) = s a)

include he in
/-- The comparison carries the canonical tensor transition to the actual stage transition. -/
theorem transition_comparison (I : Ideal R) (z : A ⊗[R] I) :
    comparison e (I.map (algebraMap R S))
      (IdealTensorKernel.transition (algebraMap R S)
        (AffineObstructionBaseChange.rightMap S) (AffineObstructionBaseChange.square S) I z) =
      IdealTensorKernel.transition (algebraMap R S) s hs I z := by
  induction z with
  | tmul a i =>
    simp only [IdealTensorKernel.transition_tmul, comparison, LinearEquiv.rTensor_tmul]
    change e (AffineObstructionBaseChange.rightMap S a) ⊗ₜ[S]
      IdealTensorKernel.idealTransition (algebraMap R S) I i =
      s a ⊗ₜ[S] IdealTensorKernel.idealTransition (algebraMap R S) I i
    rw [he]
  | add x y hx hy => simp only [map_add, hx, hy]

include he in
/-- Vanishing in the actual stage reflects to vanishing in its tensor presentation. -/
theorem transition_eq_zero (I : Ideal R) (z : A ⊗[R] I)
    (hz : IdealTensorKernel.transition (algebraMap R S) s hs I z = 0) :
    IdealTensorKernel.transition (algebraMap R S)
      (AffineObstructionBaseChange.rightMap S) (AffineObstructionBaseChange.square S) I z = 0 := by
  apply (comparison e (I.map (algebraMap R S))).injective
  rw [transition_comparison e s hs he, hz, map_zero]

include he in
/-- Residual flatness and actual-stage vanishing kill the entire new ideal obstruction. -/
theorem inclusion_injective (I : Ideal R)
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] A)]
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I,
      IdealTensorKernel.transition (algebraMap R S) s hs I z.val = 0) :
    Function.Injective (FCurve.idealTensorInclusion (S := B) (I.map (algebraMap R S))) := by
  have hinj := AffineObstructionBaseChange.inclusion_injective S I
    (fun z ↦ transition_eq_zero e s hs he I z.val (h z))
  intro x y hxy
  obtain ⟨x, rfl⟩ := (comparison e (I.map (algebraMap R S))).surjective x
  obtain ⟨y, rfl⟩ := (comparison e (I.map (algebraMap R S))).surjective y
  apply congrArg
  apply hinj
  apply e.injective
  simpa only [← inclusion_comparison] using hxy

end FLT.Mazur.AffineObstructionEquiv
