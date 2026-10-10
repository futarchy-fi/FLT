/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafUnitCocycleRestrict
public import FLT.Mazur.ModulePullbackTrivializationSections
public import Mathlib.Tactic.IrreducibleDef

/-!
# Sealed chart coefficients of cocycle sections

Compute chart coefficients before specializing the scheme and its cocycle.
The opaque value retains the original trivialization through its defining equality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (g : Cocycle U)

/-- The actual chart coefficient, sealed against expansion of the chart isomorphism. -/
irreducible_def chartValue (i : ι) (s : Γ(g.sheaf, ⊤)) : Γ((U i).toScheme, ⊤) :=
  (g.restrictIso i).hom.app ⊤ (g.sheaf.presheaf.map (homOfLE le_top).op s)

/-- The sealed coefficient evaluates the original component of the section. -/
theorem chartValue_evaluate (i : ι) (s : Γ(g.sheaf, ⊤)) :
    g.chartValue i s = g.evaluate i ((U i).ι_image_le ⊤)
      (g.sheaf.presheaf.map (homOfLE le_top).op s) := by
  rw [chartValue_def, restrictIso_hom_app]

/-- The actual pulled-back trivialization evaluates by pullback of the sealed coefficient. -/
theorem pullGlobal_chartValue {X : Scheme.{u}} (p : X ⟶ Y) (i : ι)
    (s : Γ(g.sheaf, ⊤)) :
    (modulePullbackTrivialization p (g.restrictIso i)).hom.app ⊤
        (((pullback p).obj g.sheaf).presheaf.map (homOfLE le_top).op
          (pullGlobal p g.sheaf s)) =
      (p ∣_ U i).appTop (g.chartValue i s) := by
  rw [chartValue_def]
  exact modulePullbackTrivialization_pullGlobal p g.sheaf (U i) (g.restrictIso i) s

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
