/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedLinePullback
public import FLT.Mazur.AmpleAffinePullback

/-!
# Generator opens for a specified line pullback

The full tensor-degree section comparison retains the exact inverse-image
open on which the original section generates its line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SectionGradedLinePullback
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] ModuleSheafTensor.tensor

variable {X Y : Scheme} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
  (hL : LocallyFreeRankOne L) (e : (pullback f).obj L ≅ M)

include hL

/-- The specified line comparison preserves the actual generator open in every degree. -/
theorem sectionMap_generatorOpen (d : ℕ) (s : Piece L ⊤ d) :
    sectionGeneratorOpen (tensorPower M d) (sectionMap f e d ⊤ s) =
      f ⁻¹ᵁ sectionGeneratorOpen (tensorPower L d) s := by
  change sectionGeneratorOpen (tensorPower M d)
    ((tensorPowerCongr e d).hom.app ⊤
      ((tensorPowerIso f L d).hom.app ⊤ (pullGlobal f _ s))) = _
  rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_iso,
    sectionGeneratorOpen_pullGlobal (hL.tensorPower d)]

end FLT.Mazur.SectionGradedLinePullback
