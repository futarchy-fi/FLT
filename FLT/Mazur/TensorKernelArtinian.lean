/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorKernelFiniteLength
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Residue-field detection of tensor exactness over Artinian rings

An augmented complex whose final term is flat is exact over an Artinian base
when it is exact after tensoring with each residue field. The same statement
holds with every coefficient module, including nonflat quotients and infinite modules.
-/

@[expose] public noncomputable section
open TensorProduct
universe v
namespace FLT.Mazur.TensorKernelArtinian
variable {R : Type v} [CommRing R]
variable {P M N : Type*}
  [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable (u : P →ₗ[R] M) (d : M →ₗ[R] N)

/-- The unit scalar tensor equivalence intertwines the original linear map. -/
lemma lid_lTensor (x : R ⊗[R] P) :
    (TensorProduct.lid R M) (u.lTensor R x) = u ((TensorProduct.lid R P) x) := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r p => simp only [LinearMap.lTensor_tmul, TensorProduct.lid_tmul, map_smul]

/-- Exactness with the regular coefficient module is exactness of the original maps. -/
lemma exact_of_tensor_regular
    (h : Function.Exact (u.lTensor R) (d.lTensor R)) : Function.Exact u d := by
  intro x
  constructor
  · intro hx
    have hz : d.lTensor R ((1 : R) ⊗ₜ[R] x) = 0 := by
      rw [LinearMap.lTensor_tmul, hx, tmul_zero]
    obtain ⟨a, ha⟩ := (h _).mp hz
    refine ⟨(TensorProduct.lid R P) a, ?_⟩
    rw [← lid_lTensor u, ha, TensorProduct.lid_tmul, one_smul]
  · rintro ⟨a, rfl⟩
    have hz := h.apply_apply_eq_zero ((1 : R) ⊗ₜ[R] a)
    have hz' := congrArg (TensorProduct.lid R N) hz
    simpa only [LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul, map_zero] using hz'

variable [IsArtinianRing R] [Module.Flat R N]

/-- All finite coefficients lift from residue-field exactness over an Artinian base. -/
theorem exact_finite_coefficients (hdu : d.comp u = 0)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact (u.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I)))
    (B : Type v) [AddCommGroup B] [Module R B] [Module.Finite R B] :
    Function.Exact (u.lTensor B) (d.lTensor B) :=
  TensorKernelFiniteLength.exact_of_residue_quotients u d hdu hres
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- Residue-field exactness implies exactness before reduction, including all nilpotents. -/
theorem exact_of_residue_fields (hdu : d.comp u = 0)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact (u.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I))) : Function.Exact u d :=
  exact_of_tensor_regular u d (exact_finite_coefficients u d hdu hres R)

/-- Residue-field exactness also controls arbitrary, possibly infinite, coefficients. -/
theorem exact_arbitrary_coefficients (hdu : d.comp u = 0)
    (hres : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact (u.lTensor (R ⧸ I)) (d.lTensor (R ⧸ I)))
    (B : Type v) [AddCommGroup B] [Module R B] :
    Function.Exact (u.lTensor B) (d.lTensor B) := by
  intro x
  constructor
  · intro hx
    obtain ⟨L, hL, hfin⟩ := exists_finite_submodule_left_of_setFinite
      ({x} : Set (B ⊗[R] M)) (Set.finite_singleton x)
    let _ := hL
    obtain ⟨a, ha⟩ := hfin (Set.mem_singleton x)
    have ha0 : d.lTensor L a = 0 := by
      apply Module.Flat.rTensor_preserves_injective_linearMap L.subtype L.subtype_injective
      rw [map_zero, ← TensorKernelExtension.differential_naturality, ha, hx]
    obtain ⟨b, hb⟩ := (exact_finite_coefficients u d hdu hres L a).mp ha0
    refine ⟨L.subtype.rTensor P b, ?_⟩
    rw [TensorKernelExtension.differential_naturality, hb, ha]
  · rintro ⟨a, rfl⟩
    have h : (d.lTensor B).comp (u.lTensor B) = 0 := by
      rw [← LinearMap.lTensor_comp, hdu, LinearMap.lTensor_zero]
    exact LinearMap.congr_fun h a

end FLT.Mazur.TensorKernelArtinian
