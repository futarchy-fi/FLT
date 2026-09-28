/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Linear retractions of finite faithfully flat algebra maps

Over a principal ideal domain, the effective equalizer of a faithfully flat
algebra map has torsion-free cokernel. A finite cokernel is consequently
projective, giving a linear retraction over the original base.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {R A B : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [Module.FaithfullyFlat A B] [Module.Flat R B]

omit [IsPrincipalIdealRing R] in
/-- The cokernel of a faithfully flat algebra map is torsion-free over a base domain. -/
theorem faithfullyFlatCokernelTorsionFree :
    Module.IsTorsionFree R (B ⧸ (IsScalarTower.toAlgHom R A B).toLinearMap.range) := by
  let f := (IsScalarTower.toAlgHom R A B).toLinearMap
  let d := (TensorProduct.includeLeftSubRight A B).restrictScalars R
  let tensorFlat : Module.Flat R (B ⊗[A] B) := Module.Flat.trans R B _
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r z hz
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective f.range z
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hb : r • b ∈ f.range := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hd : d (r • b) = 0 :=
    (IsEffective.of_faithfullyFlat A B (r • b)).mpr hb
  have hdb : d b = 0 := (smul_eq_zero.mp (by simpa only [map_smul] using hd)).resolve_left hr
  exact (IsEffective.of_faithfullyFlat A B b).mp hdb

variable [Module.Finite R B]

/-- A finite faithfully flat algebra inclusion has a linear retraction over a PID. -/
theorem faithfullyFlatLinearRetraction :
    ∃ s : B →ₗ[R] A,
      s.comp (IsScalarTower.toAlgHom R A B).toLinearMap = LinearMap.id := by
  let f := (IsScalarTower.toAlgHom R A B).toLinearMap
  let P := f.range
  let cokernelTorsionFree : Module.IsTorsionFree R (B ⧸ P) :=
    faithfullyFlatCokernelTorsionFree
  let cokernelFree : Module.Free R (B ⧸ P) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ
    (LinearMap.id : (B ⧸ P) →ₗ[R] B ⧸ P) P.mkQ_surjective
  let t : B →ₗ[R] B := LinearMap.id - s.comp P.mkQ
  have ht (b : B) : t b ∈ P := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change P.mkQ (b - s (P.mkQ b)) = 0
    have hsb : P.mkQ (s (P.mkQ b)) = P.mkQ b := LinearMap.congr_fun hs (P.mkQ b)
    rw [map_sub, hsb, sub_self]
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective A B
  let e := LinearEquiv.ofInjective f hf
  refine ⟨e.symm.toLinearMap.comp (t.codRestrict P ht), ?_⟩
  ext a
  apply e.injective
  apply Subtype.ext
  change (e (e.symm ⟨t (f a), ht (f a)⟩)).val = (e a).val
  rw [e.apply_symm_apply]
  change f a - s (P.mkQ (f a)) = f a
  rw [show P.mkQ (f a) = 0 from (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩,
    map_zero, sub_zero]

end Algebra
