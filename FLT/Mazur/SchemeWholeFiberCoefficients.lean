/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeWholeFiberGenericOpen
public import FLT.Mazur.AffineEnvelopeFiniteNeighborhood
public import FLT.Mazur.SchemeOpenEnvelopeDenominators

/-!
# Actual target coefficients retaining complete good fibers

Principal neighborhoods in the unchanged affine target construct coefficients
whose entire source principal lies in the prescribed open. At the generic
point Chevalley supplies the neighborhood from pointwise whole-fiber data.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeWholeFiberOpen
variable {Y T : Scheme.{u}} (q : Y ⟶ T) (L : Y.Opens) [IsAffine T]

/-- Every point of the whole-fiber open has an actual old target denominator. -/
theorem exists_coefficient (t : T) (ht : t ∈ locus q L) :
    ∃ r : Γ(T, ⊤), t ∈ T.basicOpen r ∧ Y.basicOpen (q.appTop r) ≤ L := by
  obtain ⟨r, hr, hU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (locus q L) {t} (Set.finite_singleton t) (Set.singleton_subset_iff.mpr ht)
  refine ⟨r, hr rfl, ?_⟩
  rw [← Scheme.Hom.preimage_basicOpen_top]
  exact (q.preimage_mono hU).trans (preimage_le q L)

/-- The full target open is exactly the union of the constructed admissible principals. -/
theorem mem_locus_iff_coefficient (t : T) : t ∈ locus q L ↔
    ∃ r : Γ(T, ⊤), t ∈ T.basicOpen r ∧ Y.basicOpen (q.appTop r) ≤ L := by
  refine ⟨exists_coefficient q L t, ?_⟩
  rintro ⟨r, hr, hL⟩
  rw [← Scheme.Hom.preimage_basicOpen_top] at hL
  exact le_locus q L (T.basicOpen r) hL hr

variable [NoetherianSpace Y] [LocallyOfFinitePresentation q] [QuasiCompact q]
  [IrreducibleSpace T]

/-- Whole generic-fiber containment constructs a nonnilpotent coefficient in the old target. -/
theorem exists_generic_coefficient
    (h : ∀ y : Y, q y = genericPoint T → y ∈ L) :
    ∃ r : Γ(T, ⊤), genericPoint T ∈ T.basicOpen r ∧
      Y.basicOpen (q.appTop r) ≤ L ∧ ¬ IsNilpotent r := by
  obtain ⟨r, hr, hL⟩ := exists_coefficient q L (genericPoint T)
    ((genericPoint_mem_iff q L).mpr h)
  refine ⟨r, hr, hL, ?_⟩
  intro hn
  have he := (Scheme.isNilpotent_iff_basicOpen_eq_bot r).mp hn
  rw [he] at hr
  exact hr

end FLT.Mazur.SchemeWholeFiberOpen
