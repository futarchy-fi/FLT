/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineLocalResidual
public import FLT.Mazur.SchemeLocalSectionEquality

/-!
# Full residual invariance on every invertible-level test

Sheaf separation descends exact local relabeling equations to the whole
test scheme. No reducedness or affine hypothesis is needed on the test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Finite invariant functions satisfy the entire arrow equation at invertible level. -/
theorem affineRelabelSections_invertible_condition (s : affineRelabelSections n i)
    {T : Scheme} (p : T ⟶ (affineResidualDomain n i).toScheme)
    (hn : IsUnit (n : Γ(T, ⊤))) :
    p.appTop ((affineResidualSource n i).appTop s.val) =
      p.appTop ((affineResidualTarget n i).appTop s.val) := by
  apply SchemeLocalSectionEquality.eq_of_locally_eq
  intro x
  obtain ⟨U, _, hx, he⟩ := affineRelabelSections_local_condition n i s p hn x
  exact ⟨U, hx, he⟩

end FLT.Mazur.CyclicCharacteristicOrbit
