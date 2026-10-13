/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryFiberLine
public import FLT.Mazur.PolygonCompleteMarkingDescendedTest

/-!
# Descended smoothing-line recovery on the full varying boundary

The line descended from an actual fppf parameter map recovers the original
whole translated boundary product. Recovery preserves the canonical section
and commutes with the original complete-family fiber comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve SchemePicard PolygonParameterTranslation PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeMarkingGluedLine completeMarkingDescentIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {V : Scheme} (s : V ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- The descended complete-family line on the actual varying translated boundary. -/
def completeDescendedBoundaryLineIso :
    (Scheme.Modules.pullback (completeMovedBoundaryMap K n h g c)).obj
      (completeMarkingGluedLine K n h s).val ≅
        movedProductMarkingLine K n hn p q hp g c (fun _ ↦ 1) :=
  (Scheme.Modules.pullback (completeMovedBoundaryMap K n h g c)).mapIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm ≪≫
      completeMovedBoundaryLineIso K n h g c

/-- Descended recovery retains the canonical section of the whole moved product. -/
theorem completeDescendedBoundaryLineIso_section :
    (Scheme.Modules.pullback (completeMovedBoundaryMap K n h g c)).map
      (completeMarkingGluedSection K n h s) ≫
        (completeDescendedBoundaryLineIso K n h s g c).hom =
          (modulePullbackUnitIso _).hom ≫
            divisorSectionMap
              (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)).1 :=
  markingAtlasSectionRecovery _ _ _ _ (completeMarkingGluedSection_original K n h s)
    _ _ _ (completeMovedBoundaryLineIso_section K n h g c).section

/-- The actual descended test recovery commutes with the original boundary-fiber comparison. -/
theorem completeDescendedBoundaryLineIso_fiber_triangle :
    LinePullbackTriangle (completeMovedBoundaryFiberIso K n h g c).hom
      (pullback.fst (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K))
      (completeMovedBoundaryMap K n h g c) (completeMovedBoundaryFiberIso_fst K n h g c)
      (completeMarkingDescendedTestIso K n h s (Over.mk (g ≫ completeClosedBase K)))
      (completeBoundaryFiberLineIso K n h g c)
      (completeDescendedBoundaryLineIso K n h s g c) :=
  (completeBoundaryFiberLineIso_triangle K n h g c).sourceIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm

end FLT.Mazur.PolygonInfinitesimalStages
