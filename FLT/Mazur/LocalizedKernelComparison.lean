/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Canonical localization of linear kernels

The comparison sends a fraction represented by a cycle to the same fraction
in the localized ambient module. Its linearity is over the localization ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.LocalizedKernelComparison

variable {R M N P : Type*} [CommRing R] (S : Submonoid R)
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Localization respects composition with its localization-ring linear structures. -/
lemma map_comp (d : M →ₗ[R] N) (e : N →ₗ[R] P) :
    (LocalizedModule.map S e).comp (LocalizedModule.map S d) =
      LocalizedModule.map S (e.comp d) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h x s => simp only [LinearMap.comp_apply, LocalizedModule.map_mk]

/-- Exact localization, regarded as maps over the localization ring. -/
lemma map_exact (d : M →ₗ[R] N) (e : N →ₗ[R] P) (h : Function.Exact d e) :
    Function.Exact (LocalizedModule.map S d) (LocalizedModule.map S e) :=
  LocalizedModule.map_exact S d e h

/-- The localized inclusion, with codomain restricted to localized cycles. -/
def kernelMap (e : N →ₗ[R] P) :
    LocalizedModule S e.ker →ₗ[Localization S] (LocalizedModule.map S e).ker :=
  (LocalizedModule.map S e.ker.subtype).codRestrict _ (fun x ↦ by
    change ((LocalizedModule.map S e).comp (LocalizedModule.map S e.ker.subtype)) x = 0
    rw [map_comp, LinearMap.comp_ker_subtype, map_zero, LinearMap.zero_apply])

/-- The canonical cycle comparison is injective. -/
lemma kernelMap_injective (e : N →ₗ[R] P) : Function.Injective (kernelMap S e) := by
  intro x y h
  exact LocalizedModule.map_injective S e.ker.subtype e.ker.injective_subtype
    (congrArg Subtype.val h)

/-- Exactness supplies every localized cycle from a fraction of original cycles. -/
lemma kernelMap_surjective (e : N →ₗ[R] P) : Function.Surjective (kernelMap S e) := by
  intro x
  obtain ⟨y, hy⟩ := (map_exact S e.ker.subtype e (LinearMap.exact_subtype_ker_map e)
    x.val).mp x.property
  exact ⟨y, Subtype.ext hy⟩

/-- Localization of the actual kernel, with the correct localization-ring action. -/
def kernelEquiv (e : N →ₗ[R] P) :
    LocalizedModule S e.ker ≃ₗ[Localization S] (LocalizedModule.map S e).ker :=
  LinearEquiv.ofBijective (kernelMap S e)
    ⟨kernelMap_injective S e, kernelMap_surjective S e⟩

/-- The kernel comparison retains the ambient fraction. -/
lemma kernelEquiv_mk (e : N →ₗ[R] P) (x : e.ker) (s : S) :
    (kernelEquiv S e (LocalizedModule.mk x s)).val = LocalizedModule.mk x.val s :=
  LocalizedModule.map_mk S e.ker.subtype x s

end FLT.Mazur.LocalizedKernelComparison
