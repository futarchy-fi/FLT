/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealResidualKernelSpan
public import FLT.Mazur.IdealTensorConnectingNaturality

/-!
# Vanishing of ideal obstructions after scalar extension

When the residual module is flat, old reduced relations generate the new
ones. Naturality and surjectivity of the connecting homomorphism therefore
turn vanishing of the old obstruction transition into injectivity of the
new ideal tensor inclusion. No injectivity of the extended presentation
map is assumed.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealObstructionScalarExtension
open ScalarExtensionUnit IdealTensorConnectingMap IdealTensorConnectingEquiv
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M] [Module.Flat R N]
  (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R)
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (he : Function.Exact f q) (hq : Function.Surjective q)
  [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]

/-- The extended connecting map vanishes if the actual old ideal obstructions map to zero. -/
theorem connecting_eq_zero
    (h : ∀ z : (I.subtype.rTensor M).ker,
      TensorProduct.map (IdealTensorKernel.idealTransition (algebraMap R S) I)
        (unit S M) z.val = 0) :
    connecting (f.baseChange S) (q.baseChange S) (lTensor_exact S he hq)
      (LinearMap.lTensor_surjective S hq) (I.map (algebraMap R S)) = 0 := by
  refine IdealResidualKernelSpan.map_eq_zero S I
    (T := ((I.map (algebraMap R S)).subtype.rTensor (S ⊗[R] M)).ker) f q he hq
    (connecting (f.baseChange S) (q.baseChange S) (lTensor_exact S he hq)
      (LinearMap.lTensor_surjective S hq) (I.map (algebraMap R S))) ?_
  intro z
  apply Subtype.ext
  change (connecting (f.baseChange S) (q.baseChange S) (lTensor_exact S he hq)
    (LinearMap.lTensor_surjective S hq) (I.map (algebraMap R S))
      (IdealResidualKernelSpan.relation S I f z)).val = 0
  have hn := IdealTensorConnectingNaturality.connecting_naturality
    (algebraMap R S) I f q (f.baseChange S) (q.baseChange S) he hq
    (lTensor_exact S he hq) (LinearMap.lTensor_surjective S hq)
    (unit S P) (unit S N) (unit S M) (differential S f) (differential S q) z
  exact hn.trans (h _)

include he hq in
/-- Vanishing of the old obstruction transition kills the entire new ideal tensor kernel. -/
theorem ideal_injective
    (h : ∀ z : (I.subtype.rTensor M).ker,
      TensorProduct.map (IdealTensorKernel.idealTransition (algebraMap R S) I)
        (unit S M) z.val = 0) :
    Function.Injective ((I.map (algebraMap R S)).subtype.rTensor (S ⊗[R] M)) := by
  have hc := connecting_eq_zero S I f q he hq h
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨w, hw⟩ := connecting_surjective (f.baseChange S) (q.baseChange S)
    (lTensor_exact S he hq) (LinearMap.lTensor_surjective S hq)
    (I.map (algebraMap R S)) ⟨z, hz⟩
  rw [hc, LinearMap.zero_apply] at hw
  exact (congrArg Subtype.val hw).symm

end FLT.Mazur.IdealObstructionScalarExtension
