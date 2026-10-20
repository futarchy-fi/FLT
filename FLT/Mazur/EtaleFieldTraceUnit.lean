/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitEtaleTraceUnit
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Trace units over arbitrary fields

The split étale calculation descends from an algebraic closure by trace base
change. A nonzero finite étale algebra has a surjective multiplication trace,
even when its dimension is divisible by the characteristic.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.EtaleFieldTraceUnit
universe u
variable (K B : Type u) [Field K] [CommRing B] [Algebra K B]
  [Algebra.Etale K B] [Nontrivial B]

omit [Nontrivial B] in
/-- Finite free multiplication traces commute with pure scalar extension. -/
theorem trace_tmul (L : Type*) [CommRing L] [Algebra K L]
    (a : L) (b : B) :
    Algebra.trace L (L ⊗[K] B) (a ⊗ₜ[K] b) =
      a * algebraMap K L (Algebra.trace K B b) := by
  let _ := Algebra.FormallyUnramified.finite_of_free K B
  have ht : a ⊗ₜ[K] b = a • ((1 : L) ⊗ₜ[K] b) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [ht, map_smul, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]
  rfl

/-- No nonzero finite étale algebra over a field has identically zero trace. -/
theorem trace_ne_zero : Algebra.trace K B ≠ 0 := by
  let _ := Algebra.FormallyUnramified.finite_of_free K B
  intro hz
  let L := AlgebraicClosure K
  let _ := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K L B
    (FaithfulSMul.algebraMap_injective K B)
  have hall (z : L ⊗[K] B) : Algebra.trace L (L ⊗[K] B) z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [trace_tmul, hz, LinearMap.zero_apply, map_zero, mul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  obtain ⟨z, hz⟩ := SplitEtaleTraceUnit.etale_trace_surjective L (L ⊗[K] B) 1
  exact one_ne_zero (hz.symm.trans (hall z))

/-- The actual multiplication trace is surjective over every residue field. -/
theorem trace_surjective : Function.Surjective (Algebra.trace K B) :=
  (LinearMap.surjective_iff_ne_zero).mpr (trace_ne_zero K B)

/-- There is an actual trace-one element, with no division by the degree. -/
theorem exists_trace_one : ∃ b : B, Algebra.trace K B b = 1 :=
  trace_surjective K B 1

end FLT.Mazur.EtaleFieldTraceUnit
