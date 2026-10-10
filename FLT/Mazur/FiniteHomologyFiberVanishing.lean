/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteModuleFiberVanishing
public import FLT.Mazur.FlatCokernelStep

/-!
# A descending step from fiberwise exactness

If the outgoing target and cokernel are flat, tensor homology injects into
the incoming cokernel. Exactness after tensoring therefore kills that tensor
homology. Finite homology vanishes if every residue-field complex is exact.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FiniteHomologyFiberVanishing
open FlatCokernelStep

universe u
variable {R M N P : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (d : M →ₗ[R] N) (e : N →ₗ[R] P) (h : e.comp d = 0)
  [Module.Flat R P] [Module.Flat R (P ⧸ e.range)]

include h in
/-- Exactness of a coefficient complex kills the corresponding tensor of homology. -/
theorem tensor_homology_subsingleton (B : Type*) [AddCommGroup B] [Module R B]
    (hex : Function.Exact (d.lTensor B) (e.lTensor B)) :
    Subsingleton (B ⊗[R] (e.ker ⧸ d.range.comap e.ker.subtype)) := by
  let _ := TensorKernelFlatCokernel.range_flat e
  have hi := LinearMap.lTensor_injective_of_exact_of_flat (cokernelToRange d e h)
    (cokernelToRange_surjective d e h) (homologyInclusion d e)
    (homologyInclusion_injective d e) (homology_cokernel_exact d e h) B
  apply (subsingleton_iff_forall_eq 0).mpr
  intro x
  apply hi
  rw [map_zero]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy, add_zero]
  | tmul b z =>
    obtain ⟨a, rfl⟩ := (d.range.comap e.ker.subtype).mkQ_surjective z
    have hx : e.lTensor B (b ⊗ₜ[R] a.val) = 0 := by
      rw [LinearMap.lTensor_tmul, a.property, tmul_zero]
    obtain ⟨y, hy⟩ := (hex _).mp hx
    have hd : d.range.mkQ.comp d = 0 := by
      ext m
      exact (Submodule.Quotient.mk_eq_zero d.range).mpr ⟨m, rfl⟩
    have hz := congrArg (d.range.mkQ.lTensor B) hy
    have hc : (d.range.mkQ.lTensor B).comp (d.lTensor B) = 0 := by
      rw [← LinearMap.lTensor_comp, hd, LinearMap.lTensor_zero]
    change ((d.range.mkQ.lTensor B).comp (d.lTensor B)) y = _ at hz
    rw [hc, LinearMap.zero_apply] at hz
    exact hz.symm

include h in
/-- Finite homology is zero if every residue-field complex is exact at that degree. -/
theorem homology_subsingleton_of_residue_fields
    [Module.Finite R (e.ker ⧸ d.range.comap e.ker.subtype)]
    (hex : ∀ p : PrimeSpectrum R,
      Function.Exact (d.lTensor p.asIdeal.ResidueField) (e.lTensor p.asIdeal.ResidueField)) :
    Subsingleton (e.ker ⧸ d.range.comap e.ker.subtype) :=
  FiniteModuleFiberVanishing.subsingleton_of_residue_fields fun p ↦
    tensor_homology_subsingleton d e h p.asIdeal.ResidueField (hex p)

end FLT.Mazur.FiniteHomologyFiberVanishing
