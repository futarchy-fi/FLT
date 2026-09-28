/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Nakayama

/-!
# Lifting freeness from a principal special fibre

For a finitely presented module, freeness modulo a regular Jacobson element
lifts to freeness. A lifted basis generates by Nakayama. The kernel of its
presentation is finitely generated; regularity makes this kernel divisible
by the same element, so a second application of Nakayama kills it.

This supplies the lifting step for a finite flat Hopf algebra over a DVR
once its special fibre is proved free over the quotient's special fibre.
It does not assert Hopf-subalgebra freeness over a field.
-/

@[expose] public noncomputable section

open scoped TensorProduct

open Module
open scoped Pointwise
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Nakayama kills a finitely generated kernel whose elements are divisible
by a Jacobson element acting regularly on the target. -/
theorem LinearMap.injective_of_ker_le_smul_of_mem_jacobson
    (f : M →ₗ[R] N) (r : R) (hr : r ∈ (⊥ : Ideal R).jacobson)
    (hreg : IsSMulRegular N r) (hfg : f.ker.FG)
    (hred : ∀ x, f x = 0 → x ∈ r • (⊤ : Submodule R M)) :
    Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {r}) _ hfg
  · rw [Submodule.ideal_span_singleton_smul]
    intro x hx
    obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
      (hred x (LinearMap.mem_ker.mp hx))
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨y, ?_, hy⟩
    apply LinearMap.mem_ker.mpr
    apply hreg
    change r • f y = r • (0 : N)
    rw [← f.map_smul, hy, LinearMap.mem_ker.mp hx, smul_zero]
  · exact (Ideal.span_singleton_le_iff_mem _).mpr hr

/-- Injectivity modulo a principal Jacobson ideal lifts when its generator
acts regularly on the target and the kernel is finitely generated. -/
theorem LinearMap.injective_of_baseChange_quotient_of_smul_regular
    (f : M →ₗ[R] N) (r : R) (hr : r ∈ (⊥ : Ideal R).jacobson)
    (hreg : IsSMulRegular N r) (hfg : f.ker.FG)
    (hf : Function.Injective (f.baseChange (R ⧸ Ideal.span {r}))) :
    Function.Injective f := by
  apply f.injective_of_ker_le_smul_of_mem_jacobson r hr hreg hfg
  intro x hx
  rw [← Submodule.ideal_span_singleton_smul]
  apply (Submodule.Quotient.mk_eq_zero _).mp
  rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  have ht : (1 ⊗ₜ[R] x : (R ⧸ Ideal.span {r}) ⊗[R] M) = 0 := by
    apply hf
    simp [hx]
  rw [ht, map_zero]

/-- Surjectivity after reduction modulo a Jacobson ideal lifts for a finite
target module. -/
theorem LinearMap.surjective_of_baseChange_quotient [Module.Finite R N]
    (f : M →ₗ[R] N) (I : Ideal R)
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hf : Function.Surjective (f.baseChange (R ⧸ I))) : Function.Surjective f := by
  apply f.surjective_of_surjective_comp_mkQ I hI
  intro z
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨y, hy⟩ := hf (1 ⊗ₜ[R] n)
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective R M (R ⧸ I)
    Ideal.Quotient.mk_surjective y
  refine ⟨x, ?_⟩
  have he := congrArg (TensorProduct.quotTensorEquivQuotSMul N I) hy
  simpa using he


/-- A finitely presented module is free if reduction modulo a principal
Jacobson ideal is free and its generator acts regularly on the module.
This is the free-special-fibre case of the local flatness criterion. -/
theorem Module.free_of_free_quotient_of_smul_regular [Nontrivial R]
    [Module.FinitePresentation R M] (r : R)
    (hr : r ∈ (⊥ : Ideal R).jacobson) (hreg : IsSMulRegular M r)
    [Module.Free (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⊗[R] M)] :
    Module.Free R M := by
  classical
  let S := R ⧸ Ideal.span {r}
  have hproper : Ideal.span {r} ≠ ⊤ := ne_top_of_le_ne_top
    (fun h => bot_ne_top (Ideal.jacobson_eq_top_iff.mp h))
    ((Ideal.span_singleton_le_iff_mem _).mpr hr)
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hproper
  let b := Module.Free.chooseBasis S (S ⊗[R] M)
  let ι := Module.Free.ChooseBasisIndex S (S ⊗[R] M)
  have : Finite ι := Module.Finite.finite_basis b
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M S
    Ideal.Quotient.mk_surjective).comp_left b
  let c : Basis ι R (ι →₀ R) := Finsupp.basisSingleOne
  let f : (ι →₀ R) →ₗ[R] M := c.constr R v
  have he : f.baseChange S = ((c.baseChange S).equiv b (Equiv.refl ι)).toLinearMap := by
    apply (c.baseChange S).ext
    intro i
    change f.baseChange S ((c.baseChange S) i) =
      ((c.baseChange S).equiv b (Equiv.refl ι)) ((c.baseChange S) i)
    rw [Basis.equiv_apply]
    simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, f,
      Basis.constr_basis, Equiv.refl_apply]
    exact congr_fun hv i
  have hfs : Function.Surjective (f.baseChange S) := by
    rw [he]
    exact LinearEquiv.surjective _
  have hf : Function.Surjective f := f.surjective_of_baseChange_quotient _
    ((Ideal.span_singleton_le_iff_mem _).mpr hr) hfs
  have hfi : Function.Injective f := f.injective_of_baseChange_quotient_of_smul_regular r hr hreg
    (Module.FinitePresentation.fg_ker f hf) (by rw [he]; exact LinearEquiv.injective _)
  exact Module.Free.of_basis (c.map (LinearEquiv.ofBijective f ⟨hfi, hf⟩))
