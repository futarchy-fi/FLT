/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocallyRingedSectionPointIdeal

/-!
# Ideal unit loci computed on their actual generators

Locality of the stalk rings makes the unit locus of a generated ideal the
union of the unit loci of its generators. No affine presentation or finite
generation hypothesis is required.
-/

@[expose] public noncomputable section
open AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur
universe u
variable (X : LocallyRingedSpace.{u}) (W : Opens X)

/-- The unit locus of a span is already covered by the actual original generators. -/
theorem sectionIdealOpen_span_generators (S : Set (X.presheaf.obj (op W))) :
    sectionIdealOpen X.toRingedSpace W (Ideal.span S) =
      ⨆ s : S, X.toRingedSpace.basicOpen s.val := by
  ext x
  constructor
  · intro hx
    have hxW := sectionIdealOpen_le X.toRingedSpace W (Ideal.span S) hx
    by_contra hn
    have hle : Ideal.span S ≤ sectionPointIdeal X W ⟨x, hxW⟩ := by
      apply Ideal.span_le.mpr
      intro s hs
      apply (mem_sectionPointIdeal X W ⟨x, hxW⟩ s).mpr
      intro hxs
      exact hn (Opens.mem_iSup.mpr ⟨⟨s, hs⟩, hxs⟩)
    exact (notMem_sectionIdealOpen_iff X W (Ideal.span S) ⟨x, hxW⟩).mpr hle hx
  · intro hx
    obtain ⟨s, hs⟩ := Opens.mem_iSup.mp hx
    exact (mem_sectionIdealOpen X.toRingedSpace W (Ideal.span S) x).mpr
      ⟨s.val, Ideal.subset_span s.property, hs⟩

end FLT.Mazur
