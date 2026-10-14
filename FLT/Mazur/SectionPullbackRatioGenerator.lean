/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPullbackRatioCoordinates

/-!
# Actual tensor ratios on inverse images of generator opens

The geometric generator-open condition constructs the required section isomorphism.
The resulting named ratio retains the actual open-chart ratio and principal ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  (e : (pullback f).obj L ≅ structureModule X) (hL : LocallyFreeRankOne L)
  (m : ℕ) (s : Γ(tensorPower L m, ⊤))
  (hs : f ⁻¹ᵁ sectionGeneratorOpen (tensorPower L m) s = ⊤)

include e hL hs in
/-- Generation on the actual inverse image constructs the pulled section isomorphism. -/
theorem pulledTensorSection_isIso :
    IsIso (globalSectionHom _ (pullGlobal f (tensorPower L m) s)) :=
  globalSectionHom_isIso_of_coordinate _ _
    (tensorPowerIso f L m ≪≫ tensorPowerTrivialization e m)
    (pulledFrameCoordinate_isUnit f L e hL m s hs)

/-- The actual ratio of pulled tensor sections, with generation supplied geometrically. -/
irreducible_def pulledTensorRatio (t : Γ(tensorPower L m, ⊤)) : Γ(X, ⊤) :=
  let _ := pulledTensorSection_isIso f L e hL m s hs
  sectionRatio _ (pullGlobal f (tensorPower L m) s) (pullGlobal f (tensorPower L m) t)

/-- The geometrically defined ratio retains the numerator's full coordinate ideal. -/
theorem pulledTensorRatio_span (t : Γ(tensorPower L m, ⊤)) :
    Ideal.span {pulledTensorRatio f L e hL m s hs t} =
      Ideal.span {pulledFrameCoordinate f L e m t} := by
  let _ := pulledTensorSection_isIso f L e hL m s hs
  rw [pulledTensorRatio_def]
  exact pulledFrameCoordinate_ratio_span f L e m s t

/-- On open charts this is the original local section ratio under the structure-sheaf map. -/
theorem pulledTensorRatio_eq_openRatio [IsOpenImmersion f]
    (hf : f ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower L m) s)
    (t : Γ(tensorPower L m, ⊤)) :
    pulledTensorRatio f L e hL m s hs t =
      (f.appIso ⊤).hom (sectionRatioOn (tensorPower L m) s (f ''ᵁ ⊤) hf t) := by
  let _ := pulledTensorSection_isIso f L e hL m s hs
  rw [pulledTensorRatio_def]
  exact (sectionRatioOn_openPullback f (tensorPower L m) s t hf).symm

end FLT.Mazur.FCurve
