/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingLineCocycle
public import FLT.Mazur.RelativePicardPresheaf

/-!
# Functorial marked-line comparisons on actual complete-family tests

Every morphism of parameter schemes induces the existing canonical map of
original total spaces. The ample product-marking line has section-preserving
comparisons on these maps, with the actual identity and composition equations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking tensorPowerPullbackComparison relativeTotalMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S T U : Over (Spec (.of (PowerSeries K)))}

/-- The actual ample marked-line comparison induced by a morphism of parameter tests. -/
irreducible_def completeMarkingTestLineIso (g : S ⟶ T) :
    (Scheme.Modules.pullback (relativeTotalMap (exactVeroneseProjToBase K n h) g)).obj
      (completeFiberMarkingLine K n h T.hom) ≅ completeFiberMarkingLine K n h S.hom :=
  completeMarkingLineTransitionIso K n h T.hom S.hom _ (relativeTotalMap_fst _ g)

/-- Every actual parameter-test comparison preserves the complete-family marking section. -/
theorem completeMarkingTestLineIso_section (g : S ⟶ T) :
    DivisorLineSectionCompatible (relativeTotalMap (exactVeroneseProjToBase K n h) g)
      (completeFiberMarkingDivisor_relativeCartier K n h T.hom).1
      (completeFiberMarkingDivisor_relativeCartier K n h S.hom).1
      (completeMarkingTestLineIso K n h g) := by
  rw [completeMarkingTestLineIso_def]
  exact completeMarkingLineTransitionIso_section _ _ _ _ _ _ _

/-- Actual parameter-test composition retains its original total-space transport. -/
theorem completeMarkingTestLineIso_comp (g : S ⟶ T) (k : T ⟶ U) :
    LinePullbackTriangle (relativeTotalMap (exactVeroneseProjToBase K n h) g)
      (relativeTotalMap (exactVeroneseProjToBase K n h) k)
      (relativeTotalMap (exactVeroneseProjToBase K n h) (g ≫ k))
      (relativeTotalMap_comp _ g k).symm (completeMarkingTestLineIso K n h k)
      (completeMarkingTestLineIso K n h g) (completeMarkingTestLineIso K n h (g ≫ k)) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMarkingTestLineIso_section K n h k)
    (completeMarkingTestLineIso_section K n h g)
    (completeMarkingTestLineIso_section K n h (g ≫ k))

/-- Identity on the original parameter test gives the transported sheaf pullback unitor. -/
theorem completeMarkingTestLineIso_id (S : Over (Spec (.of (PowerSeries K)))) :
    completeMarkingTestLineIso K n h (𝟙 S) =
      (Scheme.Modules.pullbackCongr (relativeTotalMap_id _ S)).app _ ≪≫
        (Scheme.Modules.pullbackId _).app (completeFiberMarkingLine K n h S.hom) :=
  (completeMarkingTestLineIso_section K n h (𝟙 S)).eq_id (relativeTotalMap_id _ S)

/-- Every tensor degree retains composition on the actual original family tests. -/
theorem completeMarkingTestLineIso_power_comp (g : S ⟶ T) (k : T ⟶ U) (d : ℕ) :
    LinePullbackTriangle (relativeTotalMap (exactVeroneseProjToBase K n h) g)
      (relativeTotalMap (exactVeroneseProjToBase K n h) k)
      (relativeTotalMap (exactVeroneseProjToBase K n h) (g ≫ k))
      (relativeTotalMap_comp _ g k).symm
      (tensorPowerPullbackComparison _ (completeMarkingTestLineIso K n h k) d)
      (tensorPowerPullbackComparison _ (completeMarkingTestLineIso K n h g) d)
      (tensorPowerPullbackComparison _ (completeMarkingTestLineIso K n h (g ≫ k)) d) :=
  (completeMarkingTestLineIso_comp K n h g k).tensorPower d

end FLT.Mazur.PolygonInfinitesimalStages
