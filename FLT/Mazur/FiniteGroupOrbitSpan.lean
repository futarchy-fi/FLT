/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Finite linear combinations of orbit functions

Orbit functions span a submodule of all functions on the group. Multiplication
preserves this span, so separating functions can be multiplied without losing
their expression as finite linear combinations of original orbit functions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]

/-- The values of one original function under all group elements. -/
def orbitProfile (a : A) : G → A := fun g ↦ g • a

/-- Finite source-linear combinations of the actual orbit profiles. -/
def orbitSpan : Submodule A (G → A) := Submodule.span A (Set.range (orbitProfile G A))

/-- Every original orbit profile lies in the span. -/
theorem orbitProfile_mem (a : A) : orbitProfile G A a ∈ orbitSpan G A :=
  Submodule.subset_span ⟨a, rfl⟩

/-- The constant unit is itself an orbit profile. -/
theorem one_mem_orbitSpan : (1 : G → A) ∈ orbitSpan G A := by
  have h : orbitProfile G A 1 = 1 := funext fun g ↦ smul_one g
  rw [← h]
  exact orbitProfile_mem G A 1

/-- All constant source functions belong to the span. -/
theorem constant_mem_orbitSpan (a : A) : (fun _ : G ↦ a) ∈ orbitSpan G A := by
  have h : (fun _ : G ↦ a) = a • (1 : G → A) := by
    ext g
    exact (mul_one a).symm
  rw [h]
  exact (orbitSpan G A).smul_mem a (one_mem_orbitSpan G A)

/-- Products of orbit profiles are the profile of the original product. -/
theorem orbitProfile_mul (a b : A) :
    orbitProfile G A (a * b) = orbitProfile G A a * orbitProfile G A b :=
  funext fun g ↦ MulSemiringAction.smul_mul g a b

/-- Finite orbit combinations are closed under multiplication. -/
theorem orbitSpan_mul {x y : G → A} (hx : x ∈ orbitSpan G A) (hy : y ∈ orbitSpan G A) :
    x * y ∈ orbitSpan G A := by
  apply Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ orbitSpan G A)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    rw [← orbitProfile_mul]
    exact orbitProfile_mem G A (a * b)
  · intro y _
    simpa only [zero_mul] using (orbitSpan G A).zero_mem
  · intro x _
    simpa only [mul_zero] using (orbitSpan G A).zero_mem
  · intro x y z _ _ _ hx hy
    simpa only [add_mul] using (orbitSpan G A).add_mem hx hy
  · intro x y z _ _ _ hy hz
    simpa only [mul_add] using (orbitSpan G A).add_mem hy hz
  · intro a x y _ _ h
    simpa only [smul_mul_assoc] using (orbitSpan G A).smul_mem a h
  · intro a x y _ _ h
    simpa only [mul_smul_comm] using (orbitSpan G A).smul_mem a h

/-- Any finite product of constructed orbit combinations is still an orbit combination. -/
theorem orbitSpan_prod {ι : Type*} (s : Finset ι) (v : ι → G → A)
    (hv : ∀ i ∈ s, v i ∈ orbitSpan G A) : ∏ i ∈ s, v i ∈ orbitSpan G A := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using one_mem_orbitSpan G A
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact orbitSpan_mul G A (hv i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ hv j (Finset.mem_insert_of_mem hj))

end FLT.Mazur.FiniteGroupQuotient
