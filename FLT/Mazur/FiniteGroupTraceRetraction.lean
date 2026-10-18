/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeBoundaryLift
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear trace functionals for a free finite action

A trace-one weight retracts the original invariant inclusion as a module map.
The construction uses no division by the group order.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
  {A : Type*} [CommRing A] [MulSemiringAction G A]

/-- Pairing with a fixed weight followed by the original orbit trace. -/
def weightedTraceLinear (a : A) : A →ₗ[invariantRing G A] invariantRing G A where
  toFun x := orbitTrace G (a * x)
  map_add' x y := by rw [mul_add, orbitTrace_add]
  map_smul' b x := by
    change orbitTrace G (a * (b.val * x)) = b * orbitTrace G (a * x)
    rw [mul_left_comm, orbitTrace_mul_invariant]

/-- Evaluation on an invariant is multiplication by the trace of the weight. -/
theorem weightedTraceLinear_inclusion (a : A) (b : invariantRing G A) :
    weightedTraceLinear G a (inclusion G A b) = b * orbitTrace G a := by
  change orbitTrace G (a * b.val) = _
  rw [mul_comm, orbitTrace_mul_invariant]

omit [Fintype G] in
/-- Freeness constructs a linear retraction of the actual invariant coordinate inclusion. -/
theorem exists_invariant_linear_retraction [Finite G]
    (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤) :
    ∃ r : A →ₗ[invariantRing G A] invariantRing G A,
      ∀ b : invariantRing G A, r (inclusion G A b) = b := by
  let _ := Fintype.ofFinite G
  obtain ⟨a, ha⟩ := exists_orbitTrace_one G hfree
  exact ⟨weightedTraceLinear G a, fun b ↦ by
    rw [weightedTraceLinear_inclusion, ha, mul_one]⟩

end FLT.Mazur.FiniteGroupQuotient
