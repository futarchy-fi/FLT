/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicUniformTrace
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # The completed cyclotomic union inside the original C_p -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The original embedding of the algebraic cyclotomic union into C_p. -/
def complexCyclotomicUnionMap : padicCyclotomicUnion p →ₗ[ℚ_[p]] ℂ_[p] :=
  ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp
    (padicCyclotomicUnion p).val).toLinearMap

/-- The completed union, realized as a closed subspace of the original C_p. -/
def complexCyclotomicClosure : Submodule ℚ_[p] ℂ_[p] :=
  (complexCyclotomicUnionMap p).range.topologicalClosure

/-- Membership is precisely closure of the original embedded union. -/
theorem mem_complexCyclotomicClosure (x : ℂ_[p]) :
    x ∈ complexCyclotomicClosure p ↔
      x ∈ closure (Set.range (fun b : padicCyclotomicUnion p ↦
        ((b : PadicAlgCl p) : ℂ_[p]))) := Iff.rfl

/-- Embed the algebraic union into its actual closure. -/
def complexCyclotomicInclusion : padicCyclotomicUnion p →ₗ[ℚ_[p]] complexCyclotomicClosure p :=
  (complexCyclotomicUnionMap p).codRestrict (complexCyclotomicClosure p)
    (fun x ↦ subset_closure (LinearMap.mem_range_self _ x))

/-- The inclusion is the original algebraic completion map on elements. -/
@[simp] theorem complexCyclotomicInclusion_coe (x : padicCyclotomicUnion p) :
    (complexCyclotomicInclusion p x : ℂ_[p]) = ((x : PadicAlgCl p) : ℂ_[p]) := rfl

/-- Norms in the closure agree with the original algebraic norm. -/
theorem complexCyclotomicInclusion_norm (x : padicCyclotomicUnion p) :
    ‖complexCyclotomicInclusion p x‖ = ‖(x : PadicAlgCl p)‖ :=
  PadicComplex.norm_extends p _

/-- The actual algebraic union is dense in this completed subspace. -/
theorem complexCyclotomicInclusion_dense : DenseRange (complexCyclotomicInclusion p) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp x.property ε hε
  exact ⟨b, hb⟩

end PadicHodgeTheory
