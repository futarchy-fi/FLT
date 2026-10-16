/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Local fractions retaining a prescribed presentation of an affine scheme

All sections on an open have local fractions whose numerators and common
basic-open denominator come from the chosen surjective presentation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffinePresentedSectionFractions
variable {B : Type*} [CommRing B] {X : Scheme} [IsAffine X]
variable (f : B →+* Γ(X, ⊤)) (hf : Function.Surjective f)

include hf in
/-- Every point has a single presented denominator for all sections on the given open. -/
theorem exists_denominator (U : X.Opens) (x : U) :
    ∃ d : B, ∃ hd : X.basicOpen (f d) ≤ U,
      x.1 ∈ X.basicOpen (f d) ∧ ∀ z : Γ(X, U), ∃ (k : ℕ) (p : B),
        X.presheaf.map (homOfLE hd).op z *
            X.presheaf.map (homOfLE le_top).op (f d) ^ k =
          X.presheaf.map (homOfLE le_top).op (f p) := by
  obtain ⟨a, ha, hx⟩ := (isAffineOpen_top X).exists_basicOpen_le x (by trivial)
  obtain ⟨d, rfl⟩ := hf a
  refine ⟨d, ha, hx, fun z ↦ ?_⟩
  obtain ⟨k, b, hb⟩ := IsLocalization.Away.surj (f d)
    (X.presheaf.map (homOfLE ha).op z)
  obtain ⟨p, rfl⟩ := hf b
  exact ⟨k, p, hb⟩

/-- The denominator used by a local fraction is an actual unit on its whole basic open. -/
theorem denominator_isUnit (d : B) :
    IsUnit (X.presheaf.map (homOfLE (show X.basicOpen (f d) ≤ ⊤ from le_top)).op
      (f d)) := by
  exact IsLocalization.Away.algebraMap_isUnit (f d)

end FLT.Mazur.AffinePresentedSectionFractions
