/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianPointLine
public import FLT.Mazur.PolygonSinglePointLineNormalization

/-!
# The complete single-point line restricts to the original polygon point line

The original Cartesian closed-fiber square retains the original unit-one
section, so its line is the same single-point line used in normalization.
The comparison preserves the canonical divisor section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve PolygonSinglePointLineNormalization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The Cartesian closed-square section is the original polygon unit-one marking. -/
theorem completeCartesianMarking_closed (i : Fin n) :
    completeCartesianMarking K n h (completeClosedBase K) (completeClosedFiberInclusion K n h)
      (PolygonCyclicAtlas.toBase K n h) (completeClosedFiber_isPullback K n h) i =
        PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i := by
  symm
  apply completeCartesianMarking_unique
  · exact (completeClosedBase_marking K n h i).symm
  · exact PolygonMarkedSections.section_base K n _ 1 i

/-- The original complete section ideal restricts to the single original polygon point ideal. -/
theorem completeBaseMarking_ker_closed (i : Fin n) :
    (completeBaseMarking K n h i).ker.comap (completeClosedFiberInclusion K n h) =
      (PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i).ker :=
  (completeCartesianMarking_ker K n h (completeClosedBase K) _ _
    (completeClosedFiber_isPullback K n h) i).trans
      (congrArg Scheme.Hom.ker (completeCartesianMarking_closed K n h i))

/-- The single-point comparison uses the original polygon normalization coefficients. -/
def completePointLineClosedIso (i : Fin n) :
    (Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).obj
      (completePointLine K n h i) ≅
        pointLine K n (by omega) (PolygonCyclicAtlas.normalization K n h)
          (PolygonCyclicAtlas.nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega))
          1 i := by
  let _ := completeCartesianPointIdeal_isIso K n h (completeClosedBase K) _ _
    (completeClosedFiber_isPullback K n h) i
  exact divisorLinePullbackIsoOfEq _ (completeBaseMarking_relativeCartier K n h i).1
    (PolygonMarkedSections.section_cartier K n _ (by omega) _
      (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i).1
    (completeBaseMarking_ker_closed K n h i)

/-- The closed comparison preserves the original canonical marked section. -/
@[reassoc] theorem completePointLineClosedIso_section (i : Fin n) :
    (Scheme.Modules.pullback (completeClosedFiberInclusion K n h)).map
        (divisorSectionMap (completeBaseMarking_relativeCartier K n h i).1) ≫
      (completePointLineClosedIso K n h i).hom =
        (modulePullbackUnitIso (completeClosedFiberInclusion K n h)).hom ≫
          divisorSectionMap (PolygonMarkedSections.section_cartier K n _ (by omega) _
            (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i).1 := by
  let _ := completeCartesianPointIdeal_isIso K n h (completeClosedBase K) _ _
    (completeClosedFiber_isPullback K n h) i
  exact divisorLinePullbackIsoOfEq_section _ (completeBaseMarking_relativeCartier K n h i).1
    (PolygonMarkedSections.section_cartier K n _ (by omega) _
      (PolygonCyclicPushout.isPushout K n h (by omega)) 1 i).1
    (completeBaseMarking_ker_closed K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
