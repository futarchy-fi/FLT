/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionGeneratorUnit
public import FLT.Mazur.SectionGradedPullback
public import FLT.Mazur.SectionGradedCoordinates
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# Scalar coordinates of tensor sections in pulled line frames

The actual tensor-power comparison carries the pulled section into the given frame.
Keeping this coordinate map named avoids expanding concrete tensor sheaves in consumers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  (e : (pullback f).obj L ≅ structureModule X)

/-- The actual coordinate of a pulled tensor-power section in the chosen line frame. -/
def pulledFrameCoordinate (m : ℕ) (s : Γ(tensorPower L m, ⊤)) : Γ(X, ⊤) :=
  (tensorPowerTrivialization e m).hom.app ⊤
    ((tensorPowerIso f L m).hom.app ⊤ (pullGlobal f (tensorPower L m) s))

/-- Prepending a line section multiplies by its actual pulled scalar coordinate. -/
theorem pulledFrameCoordinate_cons (m : ℕ) (s : Γ(L, ⊤))
    (t : Γ(tensorPower L m, ⊤)) :
    pulledFrameCoordinate f L e (m + 1) (SectionGradedMultiplication.cons L m ⊤ s t) =
      (show Γ(X, ⊤) from e.hom.app ⊤ (pullGlobal f L s)) *
        pulledFrameCoordinate f L e m t := by
  change SectionGradedCoordinates.coordinate e (m + 1) ⊤
    (SectionGradedPullback.pull f L (m + 1) ⊤ _) = _
  rw [SectionGradedPullback.pull_cons]
  exact SectionGradedCoordinates.coordinate_cons e m ⊤ _ _

/-- A tensor section generating on the source has a unit coordinate in every pulled frame. -/
theorem pulledFrameCoordinate_isUnit (hL : LocallyFreeRankOne L) (m : ℕ)
    (s : Γ(tensorPower L m, ⊤))
    (hs : f ⁻¹ᵁ sectionGeneratorOpen (tensorPower L m) s = ⊤) :
    IsUnit (pulledFrameCoordinate f L e m s) := by
  let eₘ := tensorPowerIso f L m ≪≫ tensorPowerTrivialization e m
  exact sectionFrameCoordinate_isUnit_of_generatorOpen _ eₘ _
    ((sectionGeneratorOpen_pullGlobal (hL.tensorPower m) f s).trans hs)

end FLT.Mazur.FCurve
