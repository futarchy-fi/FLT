/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteTargetFppfImage

/-!
# Exact finite target loci commute with flat locally presented base change

An actual finite neighborhood upstairs descends through its open image.
Thus flat locally finitely presented base change both preserves and detects
membership in the whole-preimage finite target locus, without surjectivity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P D B A : Scheme} {a : P ⟶ D} {b : P ⟶ B} {p : D ⟶ A} {g : B ⟶ A}
  (H : IsPullback a b p g) [IsSeparated p] [LocallyQuasiFinite p]
  [LocallyOfFiniteType p] [Flat g] [LocallyOfFinitePresentation g]

include H in
/-- Finite neighborhoods descend at every point of a flat locally presented test. -/
theorem finiteTargetOpen_le_preimage_of_fppf :
    finiteTargetOpen b ≤ g ⁻¹ᵁ finiteTargetOpen p := by
  intro x hx
  obtain ⟨U, hU, hxU⟩ := (mem_finiteTargetOpen b x).mp hx
  let _ := hU
  exact flatImage_le_finiteTarget H U ⟨x, hxU, rfl⟩

include H in
/-- Equality of exact finite loci under flat locally finitely presented base change. -/
theorem finiteTargetOpen_fppf_baseChange :
    finiteTargetOpen b = g ⁻¹ᵁ finiteTargetOpen p :=
  le_antisymm (finiteTargetOpen_le_preimage_of_fppf H) (preimage_finiteTargetOpen_le H)

include H in
/-- A single point above the target detects an actual finite neighborhood downstairs. -/
theorem mem_finiteTargetOpen_fppf_iff (x : B) :
    x ∈ finiteTargetOpen b ↔ g x ∈ finiteTargetOpen p := by
  rw [finiteTargetOpen_fppf_baseChange H]
  rfl

end FLT.Mazur.SchemeOpenEnvelope
