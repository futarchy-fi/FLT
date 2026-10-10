/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalSectionPullback
public import Mathlib.Tactic.IrreducibleDef

/-!
# Sealed composition comparison for stage pullbacks

Seal the component isomorphism before specializing schemes. Its defining equality
retains exactly the composition and equality comparisons of module pullbacks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (r : X ⟶ Y)
  (h : r ≫ q = p) (L : S.Modules)

/-- The original composite stage comparison, with its components kept opaque. -/
irreducible_def pullbackStageIso :
    (pullback r).obj ((pullback q).obj L) ≅ (pullback p).obj L :=
  (pullbackComp r q).app L ≪≫ (pullbackCongr h).app L

/-- The sealed comparison has precisely the two original morphism factors. -/
theorem pullbackStageIso_hom :
    (pullbackStageIso p q r h L).hom =
      (pullbackComp r q).hom.app L ≫ (pullbackCongr h).hom.app L := by
  rw [pullbackStageIso_def]
  rfl

end FLT.Mazur.FCurve
