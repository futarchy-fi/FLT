/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingLineTransition
public import FLT.Mazur.DivisorLineSectionIdentity
public import FLT.Mazur.DivisorLineTensorSectionCompatibility

/-!
# Identity and cocycle for the actual complete-family marking line

Transitions between original test total spaces compose on the actual ample
marked line. Identity is the pullback unitor; every tensor power retains the
same compositor equations and original canonical marking section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking tensorPowerPullbackComparison
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S T U : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (t : T ⟶ Spec (.of (PowerSeries K))) (u : U ⟶ Spec (.of (PowerSeries K)))
  (r : pullback (exactVeroneseProjToBase K n h) t ⟶
    pullback (exactVeroneseProjToBase K n h) s)
  (v : pullback (exactVeroneseProjToBase K n h) u ⟶
    pullback (exactVeroneseProjToBase K n h) t)
  (wr : r ≫ pullback.fst (exactVeroneseProjToBase K n h) s =
    pullback.fst (exactVeroneseProjToBase K n h) t)
  (wv : v ≫ pullback.fst (exactVeroneseProjToBase K n h) t =
    pullback.fst (exactVeroneseProjToBase K n h) u)

/-- Transitions along consecutive original test maps satisfy the actual line cocycle. -/
theorem completeMarkingLineTransitionIso_cocycle :
    LinePullbackTriangle v r (v ≫ r) rfl
      (completeMarkingLineTransitionIso K n h s t r wr)
      (completeMarkingLineTransitionIso K n h t u v wv)
      (completeMarkingLineTransitionIso K n h s u (v ≫ r)
        (by rw [Category.assoc, wr, wv])) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMarkingLineTransitionIso_section K n h s t r wr)
    (completeMarkingLineTransitionIso_section K n h t u v wv)
    (completeMarkingLineTransitionIso_section K n h s u (v ≫ r) _)

/-- The same actual cocycle holds for every tensor degree, including degree zero. -/
theorem completeMarkingLineTransitionIso_power_cocycle (d : ℕ) :
    LinePullbackTriangle v r (v ≫ r) rfl
      (tensorPowerPullbackComparison _ (completeMarkingLineTransitionIso K n h s t r wr) d)
      (tensorPowerPullbackComparison _ (completeMarkingLineTransitionIso K n h t u v wv) d)
      (tensorPowerPullbackComparison _ (completeMarkingLineTransitionIso K n h s u (v ≫ r)
        (by rw [Category.assoc, wr, wv])) d) :=
  (completeMarkingLineTransitionIso_cocycle K n h s t u r v wr wv).tensorPower d

/-- Identity on an original test gives exactly the original sheaf pullback unitor. -/
theorem completeMarkingLineTransitionIso_id :
    completeMarkingLineTransitionIso K n h s s (𝟙 _) (Category.id_comp _) =
      (Scheme.Modules.pullbackId _).app (completeFiberMarkingLine K n h s) :=
  (completeMarkingLineTransitionIso_section K n h s s (𝟙 _)
    (Category.id_comp _)).ext (divisorLineSectionCompatible_id _)

/-- Every powered transition preserves the original product-marking section. -/
theorem completeMarkingLineTransitionIso_power_section (d : ℕ) :
    DivisorLinePowerSectionCompatible r (completeFiberMarkingDivisor_relativeCartier K n h s).1
      (completeFiberMarkingDivisor_relativeCartier K n h t).1
      (completeMarkingLineTransitionIso K n h s t r wr) d :=
  (completeMarkingLineTransitionIso_section K n h s t r wr).tensorPower_section d

end FLT.Mazur.PolygonInfinitesimalStages
