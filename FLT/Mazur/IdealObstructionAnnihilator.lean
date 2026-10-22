/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealObstructionUnitCriterion

/-!
# Maps annihilating the scalar-extension obstruction

Residual flatness makes the old obstruction images generate the new kernel.
Consequently a linear map can kill the whole new obstruction even when the
old images become zero only after applying that map, as happens in localization.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.IdealObstructionAnnihilator
open ScalarExtensionUnit IdealTensorConnectingMap IdealTensorConnectingEquiv
variable {R P N M : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
  [AddCommGroup M] [Module R M] [Module.Flat R N]
  (S : Type*) [CommRing S] [Algebra R S] (I : Ideal R)
  (f : P →ₗ[R] N) (q : N →ₗ[R] M)
  (he : Function.Exact f q) (hq : Function.Surjective q)
  [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)]
  {T : Type*} [AddCommGroup T] [Module S T]
  (g : (I.map (algebraMap R S)) ⊗[S] (S ⊗[R] M) →ₗ[S] T)

include he hq in
/-- Annihilating old obstruction images annihilates every new ideal obstruction. -/
theorem map_kernel_eq_zero
    (h : ∀ z : (I.subtype.rTensor M).ker,
      g (TensorProduct.map (IdealTensorKernel.idealTransition (algebraMap R S) I)
        (unit S M) z.val) = 0)
    (z : ((I.map (algebraMap R S)).subtype.rTensor (S ⊗[R] M)).ker) : g z.val = 0 := by
  let c := connecting (f.baseChange S) (q.baseChange S) (lTensor_exact S he hq)
    (LinearMap.lTensor_surjective S hq) (I.map (algebraMap R S))
  have hc : (g.comp (LinearMap.ker _).subtype).comp c = 0 := by
    apply IdealResidualKernelSpan.map_eq_zero S I f q he hq
    intro w
    change g (c (IdealResidualKernelSpan.relation S I f w)).val = 0
    have hn := IdealTensorConnectingNaturality.connecting_naturality
      (algebraMap R S) I f q (f.baseChange S) (q.baseChange S) he hq
      (lTensor_exact S he hq) (LinearMap.lTensor_surjective S hq)
      (unit S P) (unit S N) (unit S M) (differential S f) (differential S q) w
    exact (congrArg g hn).trans (h _)
  obtain ⟨w, hw⟩ := connecting_surjective (f.baseChange S) (q.baseChange S)
    (lTensor_exact S he hq) (LinearMap.lTensor_surjective S hq)
    (I.map (algebraMap R S)) z
  have hh := LinearMap.congr_fun hc w
  change g (c w).val = 0 at hh
  rw [show c w = z from hw] at hh
  exact hh

omit [Module.Flat R N] in
/-- The annihilator criterion requires no chosen presentation. -/
theorem map_kernel_eq_zero_of_residual_flat
    (h : ∀ z : (I.subtype.rTensor M).ker,
      g (TensorProduct.map (IdealTensorKernel.idealTransition (algebraMap R S) I)
        (unit S M) z.val) = 0)
    (z : ((I.map (algebraMap R S)).subtype.rTensor (S ⊗[R] M)).ker) : g z.val = 0 := by
  generalize hqdef : LocalIdealTensorCriterion.presentation (R := R) M = q₀
  have hq₀ : Function.Surjective q₀ := by
    rw [← hqdef]
    exact LocalIdealTensorCriterion.presentation_surjective M
  exact map_kernel_eq_zero (R := R) (P := q₀.ker) (N := M →₀ R)
    S I q₀.ker.subtype q₀ (LinearMap.exact_subtype_ker_map q₀) hq₀ g h z

end FLT.Mazur.IdealObstructionAnnihilator
