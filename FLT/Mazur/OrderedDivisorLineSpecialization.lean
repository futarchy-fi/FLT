/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedDivisorSectionSpecialization
public import FLT.Mazur.RelativeCartierOriginalSquare
public import FLT.Mazur.DivisorLinePullback

/-!
# The full divisor line on the original curve

The cartesian specialization identifies the actual ideal modules, so duality
recovers the positive divisor line, including the canonical divisor section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.OrderedCurvePower
open FCurve
variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f]
  (a : S ⟶ space f n) (ha : a ≫ base f n = 𝟙 S)
  (I : X.IdealSheafData) (hI : EffectiveCartier I)
  (he : (divisorIdeal f n).comap (sectionCurveMap f n a ha) = I)

/-- The actual universal positive divisor line specializes to the original divisor line. -/
def divisorLineSectionIso :
    (Scheme.Modules.pullback (sectionCurveMap f n a ha)).obj (divisorLine f n) ≅
      divisorLineBundle I hI := by
  let _ := relativeCartierIdealPullback_originalSquare
    (sectionCurveMap_isPullback f n a ha) _ (divisor_relativeEffectiveCartier f n)
  exact divisorLinePullbackIsoOfEq _ (divisor_relativeEffectiveCartier f n).1 hI he

/-- The original divisor's canonical section is preserved by the specialization. -/
@[reassoc]
lemma divisorLineSectionIso_section :
    (Scheme.Modules.pullback (sectionCurveMap f n a ha)).map (divisorSection f n) ≫
      (divisorLineSectionIso f n a ha I hI he).hom =
    (modulePullbackUnitIso (sectionCurveMap f n a ha)).hom ≫ divisorSectionMap hI := by
  let _ := relativeCartierIdealPullback_originalSquare
    (sectionCurveMap_isPullback f n a ha) _ (divisor_relativeEffectiveCartier f n)
  exact divisorLinePullbackIsoOfEq_section _ (divisor_relativeEffectiveCartier f n).1 hI he

end FLT.Mazur.OrderedCurvePower
