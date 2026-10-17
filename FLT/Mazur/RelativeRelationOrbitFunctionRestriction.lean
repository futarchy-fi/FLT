/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationGeneratorNaturality
public import FLT.Mazur.InvariantOpenRelationFunctions

/-!
# Restricting orbit functions in actual open-scheme coordinates

Restriction of invariant sections is the pullback along the inclusion of the
original source opens. The equation also holds after any scheme-valued test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.RelativeRelationOrbit
open InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{0}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q)
  {O W : TopologicalSpace.Opens (Orbit e)} (h : O ≤ W)

/-- The source inclusion pulls an invariant function back to its restricted section. -/
theorem orbitFunctions_restriction (t : (invariantSheaf e).obj.obj (op W)) :
    (Scheme.homOfLE _ (show (pullOpen e O).val ≤ (pullOpen e W).val
      from fun _ hx ↦ h hx)).appTop (orbitFunctions e W t).val =
        (orbitFunctions e O ((invariantSheaf e).obj.map (homOfLE h).op t)).val := by
  change (Scheme.homOfLE _ _).appTop
    ((pullOpen e W).val.topIso.inv ((invariantInclusion e).hom.app (op W) t)) = _
  rw [homOfLE_appTop_coordinates]
  exact congrArg (pullOpen e O).val.topIso.inv (invariantInclusion_restrict e h t).symm

/-- Arbitrary scheme tests retain the same exact restriction equation. -/
theorem orbitFunctions_restriction_test (t : (invariantSheaf e).obj.obj (op W))
    {T : Scheme} (a : T ⟶ (pullOpen e O).val.toScheme) :
    (a ≫ Scheme.homOfLE _ (show (pullOpen e O).val ≤ (pullOpen e W).val
      from fun _ hx ↦ h hx)).appTop (orbitFunctions e W t).val =
        a.appTop (orbitFunctions e O ((invariantSheaf e).obj.map (homOfLE h).op t)).val := by
  change a.appTop ((Scheme.homOfLE _ _).appTop _) = _
  rw [orbitFunctions_restriction]

end FLT.Mazur.RelativeRelationOrbit
