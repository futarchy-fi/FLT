/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange

/-!
# Smooth loci on specified Cartesian squares

Retain the supplied projections when using the arbitrary base-change formula.
This allows the same formula to apply to a universal translation square.
-/

public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur
universe u

/-- The smooth locus formula retains every supplied Cartesian presentation. -/
theorem smoothLocus_preimage_of_isPullback {X S T P : Scheme.{u}}
    {f : X ⟶ S} {g : T ⟶ S} {a : P ⟶ X} {b : P ⟶ T}
    (H : IsPullback a b f g) [Flat f] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation b] : a ⁻¹ᵁ f.smoothLocus = b.smoothLocus := by
  rw [← H.isoPullback_hom_fst, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_smoothLocus_baseChange, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact H.isoPullback_hom_snd

end FLT.Mazur
