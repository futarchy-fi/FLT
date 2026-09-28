/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Trace-dual lattices under scalar extension

The trace pairing of a separable field extension stays nondegenerate after
extending scalars, even when the resulting algebra is a product of fields.
Its dual basis and the trace-dual lattice commute with this scalar extension.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Module Algebra

variable {K L F ι : Type*} [Field K] [Field L] [Field F]
  [Algebra K L] [Algebra K F] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Finite ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Scalar extension preserves nondegeneracy of the trace pairing of a finite
separable field extension, including when the tensor algebra is not a field. -/
theorem Algebra.traceForm_nondegenerate_tensorProduct (b : Basis ι K L) :
    (traceForm F (F ⊗[K] L)).Nondegenerate := by
  classical
  let := Fintype.ofFinite ι
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b := b.baseChange F),
    ← traceMatrix_of_basis, ← discr_def, discr_baseChange]
  exact (map_ne_zero (algebraMap K F)).mpr (discr_not_zero_of_basis K b)

/-- The trace-dual basis is obtained by extending the original trace-dual basis. -/
theorem Module.Basis.traceDual_baseChange (b : Basis ι K L) :
    (traceForm F (F ⊗[K] L)).dualBasis
      (traceForm_nondegenerate_tensorProduct (F := F) b) (b.baseChange F) =
        b.traceDual.baseChange F := by
  have h := (LinearMap.BilinForm.dualBasis_eq_iff
    (traceForm_nondegenerate_tensorProduct (F := F) b) (b.baseChange F)
    (b.traceDual.baseChange F)).mpr (by
      intro i j
      simp only [traceForm_apply, Basis.baseChange_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_includeRight_of_basis b,
        Basis.trace_traceDual_mul]
      split_ifs <;> simp)
  exact DFunLike.coe_injective h

/-- The trace-dual lattice spanned by a base-changed basis is spanned by the
base change of the original trace-dual basis. -/
theorem Module.Basis.dualSubmodule_span_baseChange
    {S : Type*} [CommRing S] [Algebra S F] (b : Basis ι K L) :
    (traceForm F (F ⊗[K] L)).dualSubmodule
      (Submodule.span S (Set.range (b.baseChange F))) =
        Submodule.span S (Set.range (b.traceDual.baseChange F)) := by
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _
    (traceForm_nondegenerate_tensorProduct b), b.traceDual_baseChange]

omit [DecidableEq ι] in
/-- Extending a lattice and then taking its trace dual is the same as extending
its trace dual. The lattice is assumed to have a basis over the original ring;
the extended algebra may be a product of fields. -/
theorem Module.Basis.dualSubmodule_span_image_baseChange
    {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A K] [Algebra A L] [IsScalarTower A K L]
    [Algebra A S] [Algebra S F] [Algebra A F]
    [IsScalarTower A K F] [IsScalarTower A S F]
    (b : Basis ι K L) (N : Submodule A L)
    (hN : N = Submodule.span A (Set.range b)) :
    (traceForm F (F ⊗[K] L)).dualSubmodule
      (Submodule.span S (Algebra.TensorProduct.includeRight '' (N : Set L))) =
    Submodule.span S (Algebra.TensorProduct.includeRight ''
      ((traceForm K L).dualSubmodule N : Set L)) := by
  classical
  let f : L →ₗ[A] F ⊗[K] L :=
    (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).toLinearMap.restrictScalars A
  have hs (c : Basis ι K L) :
      Submodule.span S (f '' (Submodule.span A (Set.range c) : Set L)) =
        Submodule.span S (Set.range (c.baseChange F)) := by
    have he : Submodule.span S (f '' (Submodule.span A (Set.range c) : Set L)) =
        Submodule.span S (f '' Set.range c) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        exact (Submodule.image_span_subset f _
          ((Submodule.span S (f '' Set.range c)).restrictScalars A)).mpr
          (fun x hx ↦ Submodule.subset_span ⟨x, hx, rfl⟩)
      · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    rw [he, ← Set.range_comp]
    apply congrArg (fun g : ι → F ⊗[K] L ↦ Submodule.span S (Set.range g))
    funext i
    exact (Basis.baseChange_apply F c i).symm
  change (traceForm F (F ⊗[K] L)).dualSubmodule
      (Submodule.span S (f '' (N : Set L))) =
    Submodule.span S (f '' ((traceForm K L).dualSubmodule N : Set L))
  rw [hN, hs, LinearMap.BilinForm.dualSubmodule_span_of_basis _
    (traceForm_nondegenerate K L)]
  change _ = Submodule.span S (f '' (Submodule.span A (Set.range b.traceDual) : Set L))
  rw [hs, b.dualSubmodule_span_baseChange]
