/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricFiberSmoothLineParameters
public import FLT.Mazur.RelativePicardFppfSheaf

/-!
# Fixed ordered translation tests in the original Picard sheaf

A positive power and an ordered degree select a smooth original test and
an actual translation line on its total space. These choices are independent
of all later test schemes and sections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedCurvePower
open FCurve SchemePicard ModuleLineBundleTensorPullback
variable {X S : Scheme} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [IsSeparated f]
  {B : X.Modules} (hB : LocallyFreeRankOne B)

/-- The countable indices of the fixed translations: positive power and ordered degree. -/
abbrev SmoothTranslationIndex := ℕ+ × ℕ

/-- The original test underlying a fixed ordered translation. -/
def smoothTranslationTest (i : SmoothTranslationIndex) : Over S := Over.mk (base f i.2)

instance smoothTranslationTest_smooth (i : SmoothTranslationIndex) :
    Smooth (smoothTranslationTest f i).hom := by
  let _ := SmoothOfRelativeDimension.smooth 1 f
  exact base_smooth f i.2

/-- The actual line class on the total space of the fixed original test. -/
def smoothTranslationPicard (i : SmoothTranslationIndex) :
    Pic (pullback f (smoothTranslationTest f i).hom) :=
  mk (translationLine f i.2 (tensorPower B i.1))
    (translationLine_rankOne f i.2 (hB.tensorPower i.1))

/-- The image of the fixed translation in the original relative Picard sheaf. -/
def smoothTranslationClass (i : SmoothTranslationIndex) :
    (relativeFppfSheaf f).obj.obj (op (smoothTranslationTest f i)) :=
  relativeFppfClass f _ (relativeClass _ (smoothTranslationPicard f hB i))

/-- Restriction retains both the original relative quotient and sheafification comparison. -/
theorem smoothTranslationClass_map (i : SmoothTranslationIndex) {T : Over S}
    (a : T ⟶ smoothTranslationTest f i) :
    (relativeFppfSheaf f).obj.map a.op (smoothTranslationClass f hB i) =
      relativeFppfClass f T (relativeClass _
        (SchemePicard.pullback (relativeTotalMap f a) (smoothTranslationPicard f hB i))) := by
  rw [smoothTranslationClass, relativeFppfClass_naturality, relativeBaseMap_class]

end FLT.Mazur.OrderedCurvePower
