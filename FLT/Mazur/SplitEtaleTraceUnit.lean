/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Etale.Field

/-!
# Trace units in split finite étale algebras

The multiplication trace of a finite product is the sum of its coordinates.
A single coordinate idempotent has trace one, in every characteristic. This
constructs trace units over separably closed fields without dividing by rank.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SplitEtaleTraceUnit
open Module
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]

/-- The multiplication trace in a product algebra is the sum of its entries. -/
theorem trace_pi (x : ι → R) : Algebra.trace R (ι → R) x = ∑ i, x i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun R ι), Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  change Algebra.leftMulMatrix (Pi.basisFun R ι) x i i = x i
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  simp

omit [Fintype ι] in
/-- A coordinate idempotent is a trace-one element, independent of characteristic. -/
theorem trace_single [Finite ι] [DecidableEq ι] (i : ι) :
    Algebra.trace R (ι → R) (Pi.single i 1) = 1 := by
  classical
  let _ := Fintype.ofFinite ι
  rw [trace_pi]
  simp

omit [Fintype ι] in
/-- An inhabited split algebra has a surjective trace map. -/
theorem trace_surjective_of_split {B : Type*} [CommRing B] [Algebra R B]
    [Finite ι] [Nonempty ι] (e : B ≃ₐ[R] (ι → R)) :
    Function.Surjective (Algebra.trace R B) := by
  classical
  let _ := Fintype.ofFinite ι
  intro r
  let i : ι := Classical.choice inferInstance
  refine ⟨e.symm (Pi.single i r), ?_⟩
  rw [← Algebra.trace_eq_of_algEquiv e, AlgEquiv.apply_symm_apply, trace_pi]
  simp

variable (K B : Type u) [Field K] [CommRing B] [Algebra K B]
  [Algebra.Etale K B] [IsSepClosed K] [Nontrivial B]

/-- A nonzero finite étale algebra over a separably closed field has trace one. -/
theorem etale_trace_surjective : Function.Surjective (Algebra.trace K B) := by
  let _ := Algebra.FormallyUnramified.finite_of_free K B
  let _ : IsArtinianRing B := isArtinian_of_tower K inferInstance
  let _ := Fintype.ofFinite (PrimeSpectrum B)
  exact trace_surjective_of_split (Algebra.FormallyEtale.equivPiOfIsSepClosed K B)

end FLT.Mazur.SplitEtaleTraceUnit
