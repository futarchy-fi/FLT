/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field detection modulo nilpotents

On a quasi-compact scheme, vanishing under the actual residue-field pullbacks
is equivalent to nilpotence. This is the nonreduced version of section detection;
the compactness hypothesis supplies a uniform nilpotence exponent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeNilpotentSectionDetection
variable {X : Scheme.{u}} [CompactSpace X]

/-- Residue-field pullbacks detect nilpotence of an actual global function. -/
lemma isNilpotent_of_residue_pullback (r : Γ(X, ⊤))
    (h : ∀ x : X, (X.fromSpecResidueField x).appTop r = 0) : IsNilpotent r := by
  apply (Scheme.isNilpotent_iff_basicOpen_eq_bot r).mpr
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : (X.fromSpecResidueField x) (default : Spec (X.residueField x)) ∈
      X.basicOpen r := by simpa using hx
  change (default : Spec (X.residueField x)) ∈
    (X.fromSpecResidueField x) ⁻¹ᵁ X.basicOpen r at hx'
  rw [Scheme.preimage_basicOpen_top, h x, Scheme.basicOpen_zero] at hx'
  exact hx'

/-- Two functions agreeing at every residue-field point differ by a nilpotent. -/
lemma isNilpotent_sub_of_residue_pullback (r t : Γ(X, ⊤))
    (h : ∀ x : X, (X.fromSpecResidueField x).appTop r =
      (X.fromSpecResidueField x).appTop t) : IsNilpotent (r - t) := by
  apply isNilpotent_of_residue_pullback
  intro x
  rw [map_sub, h x, sub_self]

end FLT.Mazur.SchemeNilpotentSectionDetection
