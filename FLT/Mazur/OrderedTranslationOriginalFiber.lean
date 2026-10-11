/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedDivisorOriginalFiber
public import FLT.Mazur.OrderedDivisorTranslation
public import FLT.Mazur.AmpleAffinePullback

/-!
# Universal translation lines on the unchanged original fiber

The original cartesian square transports both the full divisor line and the
fixed line's dual. Tensor powers use the actual pullback comparison, so the
translation family remains defined over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
open FCurve ModuleSheafTensor ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor
variable {C X T S : Scheme.{u}} {c : C ⟶ X} {q : C ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (H : IsPullback c q f g) (d : ℕ) (p : Fin d → (T ⟶ C))
  (hp : ∀ i, p i ≫ q = 𝟙 T) [SmoothOfRelativeDimension 1 f] [IsSeparated f]

/-- The original fiber's full divisor line comes from the original universal divisor line. -/
def divisorLineFiberIso (I : C.IdealSheafData) (hI : EffectiveCartier I)
    (he : I = ∏ i, (p i).ker) :
    (Scheme.Modules.pullback (fiberCurveMap H d p hp)).obj (divisorLine f d) ≅
      divisorLineBundle I hI := by
  let _ := relativeCartierIdealPullback_originalSquare
    (fiberCurveMap_isPullback H d p hp) _ (divisor_relativeEffectiveCartier f d)
  exact divisorLinePullbackIsoOfEq _ (divisor_relativeEffectiveCartier f d).1 hI
    ((divisorIdeal_fiber_comap H d p hp).trans he.symm)

/-- The dual of a fixed line restricts through the actual original cartesian square. -/
def fixedDualFiberIso (A : X.Modules) (hA : LocallyFreeRankOne A) :
    (Scheme.Modules.pullback (fiberCurveMap H d p hp)).obj
      ((Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst f (base f d))).obj
        (moduleSheafDual A)) ≅ moduleSheafDual ((Scheme.Modules.pullback c).obj A) :=
  (Scheme.Modules.pullbackComp _ _).app (moduleSheafDual A) ≪≫
    (Scheme.Modules.pullbackCongr (fiberCurveMap_fst H d p hp)).app (moduleSheafDual A) ≪≫
      moduleSheafDualPullbackIso c hA

/-- The universal translation returns the original full divisor with its fixed twist removed. -/
def translationLineFiberIso (A : X.Modules) (hA : LocallyFreeRankOne A)
    (I : C.IdealSheafData) (hI : EffectiveCartier I) (he : I = ∏ i, (p i).ker) :
    (Scheme.Modules.pullback (fiberCurveMap H d p hp)).obj (translationLine f d A) ≅
      tensor (divisorLineBundle I hI) (moduleSheafDual ((Scheme.Modules.pullback c).obj A)) :=
  tensorIso _ _ _ ≪≫ ModuleSheafTensor.congr (divisorLineFiberIso H d p hp I hI he)
    (fixedDualFiberIso H d p hp A hA)

/-- Fixed ample powers specialize as the corresponding powers on the unchanged original fiber. -/
def translationPowerFiberIso (B : X.Modules) (hB : LocallyFreeRankOne B) (n : ℕ)
    (I : C.IdealSheafData) (hI : EffectiveCartier I) (he : I = ∏ i, (p i).ker) :
    (Scheme.Modules.pullback (fiberCurveMap H d p hp)).obj
      (translationLine f d (tensorPower B n)) ≅
        tensor (divisorLineBundle I hI)
          (moduleSheafDual (tensorPower ((Scheme.Modules.pullback c).obj B) n)) :=
  translationLineFiberIso H d p hp _ (hB.tensorPower n) I hI he ≪≫
    ModuleSheafTensor.congr (Iso.refl _)
      (moduleSheafDualIso _ (tensorPowerIso c B n)).symm

end FLT.Mazur.OrderedCurvePower
