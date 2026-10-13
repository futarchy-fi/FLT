/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LinePullbackTriangleSource
public import FLT.Mazur.PolygonCompleteMarkingAtlasRecovery
public import FLT.Mazur.PolygonCompleteMarkingTestLine

/-!
# Coherent recovery of the descended marking line on every parameter test

The line glued along a surjective fppf parameter map recovers on every actual
test of the complete family. Recovery commutes with the original test-map
comparisons, retaining their exact pullback compositor and marking section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking completeMarkingLineBaseChangeIso
  completeMarkingGluedLine completeMarkingDescentIso completeMarkingGluedSection
  relativeTotalMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {V : Scheme} (s : V ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]

/-- Recovery of the actual descended line on an arbitrary complete-family test. -/
def completeMarkingDescendedTestIso (T : Over (Spec (.of (PowerSeries K)))) :
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) T.hom)).obj
      (completeMarkingGluedLine K n h s).val ≅ completeFiberMarkingLine K n h T.hom :=
  (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) T.hom)).mapIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm ≪≫
      completeMarkingLineBaseChangeIso K n h T.hom

/-- The specified test recovery preserves the original marking section exactly. -/
theorem completeMarkingDescendedTestIso_section (T : Over (Spec (.of (PowerSeries K)))) :
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) T.hom)).map
      (completeMarkingGluedSection K n h s) ≫
        (completeMarkingDescendedTestIso K n h s T).hom =
          (modulePullbackUnitIso _).hom ≫
            divisorSectionMap (completeFiberMarkingDivisor_relativeCartier K n h T.hom).1 :=
  markingAtlasSectionRecovery _ _ _ _ (completeMarkingGluedSection_original K n h s)
    _ _ _ (completeMarkingLineBaseChangeIso_section K n h T.hom).section

/-- Descended recovery commutes with the original comparison for every parameter-test map. -/
theorem completeMarkingDescendedTestIso_triangle
    {S T : Over (Spec (.of (PowerSeries K)))} (g : S ⟶ T) :
    LinePullbackTriangle (relativeTotalMap (exactVeroneseProjToBase K n h) g)
      (pullback.fst (exactVeroneseProjToBase K n h) T.hom)
      (pullback.fst (exactVeroneseProjToBase K n h) S.hom) (relativeTotalMap_fst _ g)
      (completeMarkingDescendedTestIso K n h s T) (completeMarkingTestLineIso K n h g)
      (completeMarkingDescendedTestIso K n h s S) := by
  have ht := divisorLineSectionCompatible_triangle _ _ _ (relativeTotalMap_fst
    (exactVeroneseProjToBase K n h) g)
    (completeMarkingLineBaseChangeIso_section K n h T.hom)
    (completeMarkingTestLineIso_section K n h g)
    (completeMarkingLineBaseChangeIso_section K n h S.hom)
  exact ht.sourceIso ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm

/-- The existing atlas-member recovery is the restriction of the coherent test recovery. -/
theorem completeMarkingDescendedTestIso_atlas
    (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of (PowerSeries K)))) (i : 𝒰.I₀) :
    completeMarkingDescendedTestIso K n h (SchemeFppfFamily.projection 𝒰) (Over.mk (𝒰.f i)) =
      completeMarkingAtlasLineIso K n h 𝒰 i := rfl

end FLT.Mazur.PolygonInfinitesimalStages
