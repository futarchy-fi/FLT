/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingLineBaseChange
public import FLT.Mazur.DivisorLineSectionTriangle
public import FLT.Mazur.CartierIdealPullbackComparison

/-!
# Actual marked-line transitions between tests of the complete smoothing family

A map between original base-changed total spaces over the complete family
preserves the full product marking ideal. The canonical positive-line
comparison retains the vanishing section and the original base-change triangle.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S T : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (t : T ⟶ Spec (.of (PowerSeries K)))
  (r : pullback (exactVeroneseProjToBase K n h) t ⟶
    pullback (exactVeroneseProjToBase K n h) s)
  (w : r ≫ pullback.fst (exactVeroneseProjToBase K n h) s =
    pullback.fst (exactVeroneseProjToBase K n h) t)

include w in
/-- The entire original product marking ideal is preserved by every map of test total spaces. -/
theorem completeFiberMarking_transition_ideal :
    (∏ i : Fin n, (completeFiberMarking K n h s i).ker).comap r =
      ∏ i : Fin n, (completeFiberMarking K n h t i).ker := by
  rw [← completeMarkingDivisor_comap, ← Scheme.IdealSheafData.comap_comp, w,
    completeMarkingDivisor_comap]

/-- The canonical positive-line comparison for the original map of complete-family tests. -/
irreducible_def completeMarkingLineTransitionIso :
    (Scheme.Modules.pullback r).obj (completeFiberMarkingLine K n h s) ≅
      completeFiberMarkingLine K n h t := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h s).1
  let ht := (completeFiberMarkingDivisor_relativeCartier K n h t).1
  let he := completeFiberMarking_transition_ideal K n h s t r w
  let _ := idealModulePullbackHom_isIso_of_cartier r hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq r hs ht he

/-- The transition preserves the actual canonical product-marking section. -/
theorem completeMarkingLineTransitionIso_section :
    DivisorLineSectionCompatible r (completeFiberMarkingDivisor_relativeCartier K n h s).1
      (completeFiberMarkingDivisor_relativeCartier K n h t).1
      (completeMarkingLineTransitionIso K n h s t r w) := by
  let hs := (completeFiberMarkingDivisor_relativeCartier K n h s).1
  let ht := (completeFiberMarkingDivisor_relativeCartier K n h t).1
  let he := completeFiberMarking_transition_ideal K n h s t r w
  let _ := idealModulePullbackHom_isIso_of_cartier r hs (he.symm ▸ ht)
  rw [completeMarkingLineTransitionIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The original complete-family comparison preserves its canonical section. -/
theorem completeMarkingLineBaseChangeIso_section :
    DivisorLineSectionCompatible (pullback.fst (exactVeroneseProjToBase K n h) s)
      (completeMarkingDivisor_relativeCartier K n h).1
      (completeFiberMarkingDivisor_relativeCartier K n h s).1
      (completeMarkingLineBaseChangeIso K n h s) :=
  divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Transition and base change give the same comparison from the original complete family. -/
theorem completeMarkingLineTransitionIso_triangle :
    LinePullbackTriangle r (pullback.fst (exactVeroneseProjToBase K n h) s)
      (pullback.fst (exactVeroneseProjToBase K n h) t) w
      (completeMarkingLineBaseChangeIso K n h s)
      (completeMarkingLineTransitionIso K n h s t r w)
      (completeMarkingLineBaseChangeIso K n h t) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMarkingLineBaseChangeIso_section K n h s)
    (completeMarkingLineTransitionIso_section K n h s t r w)
    (completeMarkingLineBaseChangeIso_section K n h t)

end FLT.Mazur.PolygonInfinitesimalStages
