/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionPullbackFrameCoordinates
public import FLT.Mazur.ModuleSectionRatioOpenPullback

/-!
# Normalizing pulled tensor coordinates by a generating section

The actual section ratio times the denominator coordinate recovers the numerator.
A generating denominator preserves the numerator's principal ideal, so normalization
retains the first-order divisor factor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
  (e : (pullback f).obj L ≅ structureModule X) (m : ℕ)
  (s t : Γ(tensorPower L m, ⊤))
  [IsIso (globalSectionHom _ (pullGlobal f (tensorPower L m) s))]

/-- The genuine ratio satisfies the normalized coordinate multiplication equation. -/
theorem pulledFrameCoordinate_ratio_mul :
    sectionRatio _ (pullGlobal f (tensorPower L m) s)
      (pullGlobal f (tensorPower L m) t) * pulledFrameCoordinate f L e m s =
        pulledFrameCoordinate f L e m t := by
  let E := tensorPowerIso f L m ≪≫ tensorPowerTrivialization e m
  exact (Hom.app_smul E.hom _ _).symm.trans
    (congrArg (E.hom.app ⊤) (sectionRatio_smul _
      (pullGlobal f (tensorPower L m) s) (pullGlobal f (tensorPower L m) t)))

/-- Dividing by a generating denominator retains the numerator's full principal ideal. -/
theorem pulledFrameCoordinate_ratio_span :
    Ideal.span {(sectionRatio _ (pullGlobal f (tensorPower L m) s)
      (pullGlobal f (tensorPower L m) t))} =
        Ideal.span {pulledFrameCoordinate f L e m t} := by
  let E := tensorPowerIso f L m ≪≫ tensorPowerTrivialization e m
  have hs : IsUnit (pulledFrameCoordinate f L e m s) :=
    sectionFrameCoordinate_isUnit_of_generatorOpen _ E _
      (top_unique (le_moduleHomIsoOpen _ ⊤))
  exact (Ideal.span_singleton_mul_right_unit hs _).symm.trans
    (congrArg (fun a => Ideal.span {a}) (pulledFrameCoordinate_ratio_mul f L e m s t))

/-- Open-chart ratios retain the same principal ideal in the actual pulled tensor frame. -/
theorem pulledFrameCoordinate_openRatio_span [IsOpenImmersion f]
    (hf : f ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower L m) s) :
    Ideal.span {(f.appIso ⊤).hom (sectionRatioOn (tensorPower L m) s
      (f ''ᵁ ⊤) hf t)} = Ideal.span {pulledFrameCoordinate f L e m t} := by
  rw [sectionRatioOn_openPullback]
  exact pulledFrameCoordinate_ratio_span f L e m s t

end FLT.Mazur.FCurve
