/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianPointDivisor
public import FLT.Mazur.DivisorLinePullback

/-!
# The original single-point line and its Cartesian comparison

Dualize the original labeled section ideal, not the sum of all markings.
The comparison carries its canonical vanishing section to the section of the
same label on the specified family square. Label zero is available as the
origin line for a future pointed Weierstrass presentation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The positive divisor line of one specified original complete marking. -/
def completePointLine (i : Fin n) : (exactVeroneseProj K n h).Modules :=
  divisorLineBundle (completeBaseMarking K n h i).ker
    (completeBaseMarking_relativeCartier K n h i).1

variable {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The positive line of the actual retained point on the specified square. -/
def completeCartesianPointLine (i : Fin n) : Y.Modules :=
  divisorLineBundle (completeCartesianMarking K n h s p q hs i).ker
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1

/-- Each single-point line is locally free of rank one. -/
theorem completeCartesianPointLine_rankOne (i : Fin n) :
    LocallyFreeRankOne (completeCartesianPointLine K n h s p q hs i) := by
  have hc := (completeCartesianMarking_relativeCartier K n h s p q hs i).1
  exact hc.divisorLineBundle_locallyFreeRankOne

/-- Canonical pullback identifies the original single-point line with the retained one. -/
def completeCartesianPointLineIso (i : Fin n) :
    (Scheme.Modules.pullback p).obj (completePointLine K n h i) ≅
      completeCartesianPointLine K n h s p q hs i := by
  let _ := completeCartesianPointIdeal_isIso K n h s p q hs i
  exact divisorLinePullbackIsoOfEq p (completeBaseMarking_relativeCartier K n h i).1
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (completeCartesianMarking_ker K n h s p q hs i)

/-- The comparison retains the actual canonical section, including its multiplicity. -/
@[reassoc] theorem completeCartesianPointLineIso_section (i : Fin n) :
    (Scheme.Modules.pullback p).map
        (divisorSectionMap (completeBaseMarking_relativeCartier K n h i).1) ≫
      (completeCartesianPointLineIso K n h s p q hs i).hom =
        (modulePullbackUnitIso p).hom ≫
          divisorSectionMap (completeCartesianMarking_relativeCartier K n h s p q hs i).1 := by
  let _ := completeCartesianPointIdeal_isIso K n h s p q hs i
  exact divisorLinePullbackIsoOfEq_section p (completeBaseMarking_relativeCartier K n h i).1
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (completeCartesianMarking_ker K n h s p q hs i)

end FLT.Mazur.PolygonInfinitesimalStages
