/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFieldTraceUnit

/-!
# Trace units in finite free étale algebras with a section

A section keeps every residue algebra nonzero. Residue-field trace units then
force the original multiplication trace image to be the unit ideal. This uses
all relation functions, with no assumption on the invertibility of its rank.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FiniteFreeEtaleTraceUnit
universe u
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Free R B] [Module.Finite R B]

/-- Multiplication trace commutes with scalar extension of every pure tensor. -/
theorem trace_tmul (K : Type*) [CommRing K] [Algebra R K] (a : K) (b : B) :
    Algebra.trace K (K ⊗[R] B) (a ⊗ₜ[R] b) =
      a * algebraMap R K (Algebra.trace R B b) := by
  have ht : a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [ht, map_smul, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]
  rfl

variable [Algebra.Etale R B]

/-- A section of a finite free étale algebra forces its full trace image to contain one. -/
theorem trace_surjective (ε : B →ₐ[R] R) :
    Function.Surjective (Algebra.trace R B) := by
  rw [← LinearMap.range_eq_top]
  by_contra hn
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range (Algebra.trace R B)) hn
  let _ := hm
  let K := R ⧸ m
  let _ : Field K := Ideal.Quotient.field m
  let ρ : K ⊗[R] B →ₐ[K] K := Algebra.TensorProduct.lift
    (AlgHom.id K K) ((Algebra.ofId R K).comp ε) (fun _ _ ↦ Commute.all _ _)
  let _ : Nontrivial (K ⊗[R] B) := ρ.toRingHom.domain_nontrivial
  have hz (b : B) : algebraMap R K (Algebra.trace R B b) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle ⟨b, rfl⟩)
  have hall (z : K ⊗[R] B) : Algebra.trace K (K ⊗[R] B) z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => rw [trace_tmul, hz, mul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  obtain ⟨z, hz⟩ := EtaleFieldTraceUnit.exists_trace_one K (K ⊗[R] B)
  exact one_ne_zero (hz.symm.trans (hall z))

/-- A trace-one element is constructed over the unchanged coefficient ring. -/
theorem exists_trace_one (ε : B →ₐ[R] R) : ∃ b : B, Algebra.trace R B b = 1 :=
  trace_surjective R B ε 1

end FLT.Mazur.FiniteFreeEtaleTraceUnit
