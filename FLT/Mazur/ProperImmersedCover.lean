/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperCoverImmersionCriterion

/-!
# Properness from a proper surjective cover immersed in a proper ambient scheme

This criterion uses the specified maps themselves and does not replace the
structure morphism by an isomorphic or abstractly chosen one.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

/-- A proper immersed cover detects properness by closedness of its immersion. -/
theorem isProper_iff_isClosedImmersion_of_cover {Z X P S : Scheme.{u}}
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    (p : P ⟶ S) [IsProper p] (π : Z ⟶ X) [IsProper π] [Surjective π]
    (h : Z ⟶ P) [IsImmersion h] (w : h ≫ p = π ≫ f) :
    IsProper f ↔ IsClosedImmersion h := by
  constructor
  · intro hf
    let _ : IsProper (h ≫ p) := w.symm ▸ inferInstanceAs (IsProper (π ≫ f))
    let _ : IsProper h := IsProper.of_comp h p
    exact IsClosedImmersion.of_isPreimmersion h h.isClosedMap.isClosed_range
  · intro hh
    let _ : UniversallyClosed (π ≫ f) :=
      w ▸ inferInstanceAs (UniversallyClosed (h ≫ p))
    let _ : UniversallyClosed f := UniversallyClosed.of_comp_surjective π f
    exact ⟨⟩

end FLT.Mazur.Approximation
