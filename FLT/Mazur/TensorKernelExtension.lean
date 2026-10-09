/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic

/-!
# Lifting tensor kernels through coefficient extensions

Exactness of an augmented two-term complex with flat final term is preserved
under extensions of the coefficient module. This is the diagram chase needed
for infinitesimal H0 lifting: only exactness on the submodule and quotient is
assumed, and tensor right exactness constructs the lift in the middle.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.TensorKernelExtension
variable {R : Type*} [CommRing R]
variable {P M N A B C : Type*}
  [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- The original coefficient maps commute with the original differential after tensoring. -/
lemma differential_naturality (d : M →ₗ[R] N) (i : A →ₗ[R] B) (x : A ⊗[R] M) :
    d.lTensor B (i.rTensor M x) = i.rTensor N (d.lTensor A x) := by
  have h : (d.lTensor B).comp (i.rTensor M) = (i.rTensor N).comp (d.lTensor A) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  exact LinearMap.congr_fun h x

/-- Tensor cycles lift across a short exact coefficient sequence. -/
theorem exact_of_extension [Module.Flat R N]
    (u : P →ₗ[R] M) (d : M →ₗ[R] N) (hdu : d.comp u = 0)
    (i : A →ₗ[R] B) (q : B →ₗ[R] C) (hi : Function.Injective i)
    (hiq : Function.Exact i q) (hq : Function.Surjective q)
    (hA : Function.Exact (u.lTensor A) (d.lTensor A))
    (hC : Function.Exact (u.lTensor C) (d.lTensor C)) :
    Function.Exact (u.lTensor B) (d.lTensor B) := by
  have hzero (z : B ⊗[R] P) :
      d.lTensor B (u.lTensor B z) = 0 := by
    have h : (d.lTensor B).comp (u.lTensor B) = 0 := by
      rw [← LinearMap.lTensor_comp, hdu, LinearMap.lTensor_zero]
    exact LinearMap.congr_fun h z
  intro x
  constructor
  · intro hx
    have hc : d.lTensor C (q.rTensor M x) = 0 := by
      rw [differential_naturality, hx, map_zero]
    obtain ⟨c, hc⟩ := (hC _).mp hc
    obtain ⟨b, hb⟩ := LinearMap.rTensor_surjective P hq c
    have hy : q.rTensor M (x - u.lTensor B b) = 0 := by
      rw [map_sub, ← differential_naturality u q, hb, hc, sub_self]
    obtain ⟨a, ha⟩ := (rTensor_exact M hiq hq _).mp hy
    have ha0 : d.lTensor A a = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap i hi
      rw [map_zero, ← differential_naturality d i, ha, map_sub, hx, hzero, sub_self]
    obtain ⟨a', ha'⟩ := (hA a).mp ha0
    refine ⟨b + i.rTensor P a', ?_⟩
    rw [map_add, differential_naturality u i, ha', ha]
    abel
  · rintro ⟨b, rfl⟩
    exact hzero b

/-- A submodule and its actual quotient suffice for the extension step. -/
theorem exact_of_submodule [Module.Flat R N]
    (u : P →ₗ[R] M) (d : M →ₗ[R] N) (hdu : d.comp u = 0) (L : Submodule R B)
    (hL : Function.Exact (u.lTensor L) (d.lTensor L))
    (hQ : Function.Exact (u.lTensor (B ⧸ L)) (d.lTensor (B ⧸ L))) :
    Function.Exact (u.lTensor B) (d.lTensor B) :=
  exact_of_extension u d hdu L.subtype L.mkQ L.subtype_injective
    (LinearMap.exact_subtype_mkQ L) L.mkQ_surjective hL hQ

end FLT.Mazur.TensorKernelExtension
