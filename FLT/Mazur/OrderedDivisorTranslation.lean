/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedDivisorLineSpecialization
public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.CartierTensorRank
public import FLT.Mazur.LineSheafDualEvaluation

/-!
# Actual translation lines over ordered point parameters

The universal divisor line is tensored with the pullback of the dual of a
fixed original line. Its specialization is the full original divisor line
with that fixed twist removed, by an actual sheaf isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
open FCurve ModuleSheafTensor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor
variable {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f]

/-- One actual translation line on the universal curve, independent of any test line. -/
def translationLine (A : X.Modules) : (curve f d).Modules :=
  tensor (divisorLine f d)
    ((Scheme.Modules.pullback (pullback.fst f (base f d))).obj (moduleSheafDual A))

/-- The universal translation is locally free of rank one. -/
theorem translationLine_rankOne {A : X.Modules} (hA : LocallyFreeRankOne A) :
    LocallyFreeRankOne (translationLine f d A) :=
  (divisorLine_locallyFreeRankOne f d).tensor (hA.dual.pullback _)

variable (a : S ⟶ space f d) (ha : a ≫ base f d = 𝟙 S)

/-- A fixed original sheaf returns to itself on the unchanged original curve. -/
def fixedLineSectionIso (M : X.Modules) :
    (Scheme.Modules.pullback (sectionCurveMap f d a ha)).obj
      ((Scheme.Modules.pullback (pullback.fst f (base f d))).obj M) ≅ M :=
  (Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr (sectionCurveMap_fst f d a ha)).app M ≪≫
      (Scheme.Modules.pullbackId X).app M

/-- Specialization removes the fixed twist from the original full divisor line. -/
def translationLineSectionIso (A : X.Modules) (I : X.IdealSheafData)
    (hI : EffectiveCartier I)
    (he : (divisorIdeal f d).comap (sectionCurveMap f d a ha) = I) :
    (Scheme.Modules.pullback (sectionCurveMap f d a ha)).obj (translationLine f d A) ≅
      tensor (divisorLineBundle I hI) (moduleSheafDual A) :=
  ModuleLineBundleTensorPullback.tensorIso _ _ _ ≪≫
    ModuleSheafTensor.congr (divisorLineSectionIso f d a ha I hI he)
      (fixedLineSectionIso f d a ha (moduleSheafDual A))

end FLT.Mazur.OrderedCurvePower
