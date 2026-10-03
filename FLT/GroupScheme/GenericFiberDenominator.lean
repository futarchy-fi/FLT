/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# A common denominator for generic linear maps

A linear map on generic fibers with finite free source admits one nonzero
base scalar clearing every integral input. The resulting integral map is
linear; nothing here asserts that the denominator is a unit or that the
scaled map preserves a Hopf structure.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra

variable {R K M N : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Finite R M]

/-- A generic map with finite free source has one denominator and a linear
integral numerator map, valid on every integral input. -/
theorem genericFiber_exists_denominator (f : K ⊗[R] M →ₗ[K] K ⊗[R] N) :
    ∃ d : R, d ≠ 0 ∧ ∃ g : M →ₗ[R] N, ∀ x : M,
      (1 : K) ⊗ₜ[R] g x = d • f ((1 : K) ⊗ₜ[R] x) := by
  let b := Module.Free.chooseBasis R M
  let j : N →ₗ[R] K ⊗[R] N := TensorProduct.mk R K N 1
  let fR : M →ₗ[R] K ⊗[R] N :=
    (f.restrictScalars R).comp (TensorProduct.mk R K M 1)
  obtain ⟨d, hd⟩ := IsLocalizedModule.exist_integer_multiples_of_finite
    (nonZeroDivisors R) j (fun i ↦ fR (b i))
  choose y hy using hd
  let g : M →ₗ[R] N := b.constr R y
  have hg : j.comp g = (d : R) • fR := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, g, Module.Basis.constr_basis,
      LinearMap.smul_apply] using hy i
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, g, fun x ↦ ?_⟩
  exact DFunLike.congr_fun hg x

end Algebra
