/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousCochainScalarObstruction

/-!
# Exact finite patching of homogeneous cochain corrections

A partition of one combines whole-chart corrections with the original
scalar weights. The sum stays in every full boundary kernel and corrects
the unscaled error. For compatible tower rings, all orders are retained.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HomogeneousCochainCorrection
variable {R : Type*} [CommRing R] {ι : Type*}
  {A : ι → Type*} {B : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i j, CommRing (B i j)]
  [∀ i, Algebra R (A i)] [∀ i j, Algebra R (B i j)]
  (p : ∀ i j, A i →ₐ[R] B i j) (q : ∀ i j, A j →ₐ[R] B i j)
  (I : ∀ i, Ideal (A i))
  {κ : Type*} [Fintype κ] (s r : κ → R) (hs : ∑ j, r j * s j = 1)

include hs in
/-- Finite scalar corrections give an explicit homogeneous correction of the unscaled cochain. -/
theorem weighted_correction (v : ∀ i, A i) (h : κ → ∀ i, A i)
    (hh : ∀ j i, h j i ∈ I i)
    (he : ∀ j, difference p q (h j) = s j • difference p q v) :
    (∑ j, r j • h j) ∈ cochains (R := R) I ∧
      difference p q (∑ j, r j • h j) = difference p q v := by
  constructor
  · exact (cochains (R := R) I).sum_mem (fun j _ ↦ (cochains (R := R) I).smul_mem (r j) (hh j))
  · rw [map_sum]
    simp_rw [map_smul, he, smul_smul]
    rw [← Finset.sum_smul, hs, one_smul]

include hs in
/-- Original scalar membership patches without replacing the full correction image by an ideal. -/
theorem obstruction_eq_zero_of_partition (v : ∀ i, A i)
    (h : ∀ j, s j ∈ scalarIdeal p q I v) : obstruction p q I v = 0 := by
  have hm : (1 : R) ∈ scalarIdeal p q I v := by
    rw [← hs]
    exact (scalarIdeal p q I v).sum_mem (fun j _ ↦
      (scalarIdeal p q I v).mul_mem_left (r j) (h j))
  simpa only [mem_scalarIdeal, one_smul] using hm

omit [Fintype κ] in
/-- A covering family of exact admissible scalar opens forces the genuine class to vanish. -/
theorem obstruction_eq_zero_of_span (v : ∀ i, A i) (s : κ → R)
    (hspan : Ideal.span (Set.range s) = ⊤)
    (h : ∀ j, s j ∈ scalarIdeal p q I v) : obstruction p q I v = 0 := by
  have hle : Ideal.span (Set.range s) ≤ scalarIdeal p q I v :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)
  rw [hspan] at hle
  have hm : (1 : R) ∈ scalarIdeal p q I v := hle (Submodule.mem_top)
  simpa only [mem_scalarIdeal, one_smul] using hm

end FLT.Mazur.HomogeneousCochainCorrection
