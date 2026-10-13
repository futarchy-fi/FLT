/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryFiberFrames
public import FLT.Mazur.PolygonCompleteBoundaryDescended

/-!
# Descended complete-family line on the original boundary frames

The actual fppf-descended line recovers the original normalization marking and
unit node frame, preserving their canonical sections. Both recoveries commute
with the original complete-family fiber comparison and descended test recovery.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction PolygonPinching
  PolygonMarkingBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {V : Scheme} (s : V ⟶ Spec (.of (PowerSeries K)))
  [Flat s] [Surjective s] [LocallyOfFinitePresentation s]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

open SchemePicard
attribute [local irreducible] completeMarkingGluedLine completeMarkingDescentIso
variable (i : Fin n)

/-- The descended complete line recovers the original normalization marking line. -/
def completeDescendedNormalizationLineIso :
    (Scheme.Modules.pullback (completeBoundaryNormalizationMap K n h g i)).obj
      (completeMarkingGluedLine K n h s).val ≅
        normalizationMarkingLine K n hn p q hp 1 i i g :=
  (Scheme.Modules.pullback _).mapIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm ≪≫
      completeBoundaryNormalizationLineIso K n h g i

/-- Descended normalization recovery preserves the exact original marking section. -/
theorem completeDescendedNormalizationLineIso_section :
    (Scheme.Modules.pullback (completeBoundaryNormalizationMap K n h g i)).map
      (completeMarkingGluedSection K n h s) ≫
        (completeDescendedNormalizationLineIso K n h s g i).hom =
          (modulePullbackUnitIso _).hom ≫ divisorSectionMap
            (relativeCartierBaseChange (component K).hom g _
              (normalizationIdeal_relativeCartier K n hn p q hp 1 i i)).1 :=
  markingAtlasSectionRecovery _ _ _ _ (completeMarkingGluedSection_original K n h s)
    _ _ _ (completeBoundaryNormalizationLineIso_section K n h g i).section

/-- The descended complete line recovers the original empty-divisor node frame. -/
def completeDescendedNodeLineIso :
    (Scheme.Modules.pullback (completeBoundaryNodeMap K n h g i)).obj
      (completeMarkingGluedLine K n h s).val ≅ divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullback _).mapIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm ≪≫
      completeBoundaryNodeLineIso K n h g i

/-- Descended node recovery preserves the original unit section without rescaling. -/
theorem completeDescendedNodeLineIso_section :
    (Scheme.Modules.pullback (completeBoundaryNodeMap K n h g i)).map
      (completeMarkingGluedSection K n h s) ≫
        (completeDescendedNodeLineIso K n h s g i).hom =
          (modulePullbackUnitIso _).hom ≫ divisorSectionMap effectiveCartier_top :=
  markingAtlasSectionRecovery _ _ _ _ (completeMarkingGluedSection_original K n h s)
    _ _ _ (completeBoundaryNodeLineIso_section K n h g i).section

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))

/-- Normalization recovery commutes with the actual descended complete-family test. -/
theorem completeDescendedNormalizationLineIso_fiber_triangle :
    LinePullbackTriangle (completeBoundaryOriginalFiberMap K n h g c (componentι K n i ≫ p))
      (pullback.fst (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K))
      (completeBoundaryNormalizationMap K n h g i)
      (completeBoundaryOriginalFiberMap_fst K n h g c (componentι K n i ≫ p))
      (completeMarkingDescendedTestIso K n h s (Over.mk (g ≫ completeClosedBase K)))
      (completeBoundaryFiberNormalizationLineIso K n h g c i)
      (completeDescendedNormalizationLineIso K n h s g i) :=
  (completeBoundaryFiberNormalizationLineIso_triangle K n h g c i).sourceIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm

/-- Node recovery retains the same original frame through the descended test comparison. -/
theorem completeDescendedNodeLineIso_fiber_triangle :
    LinePullbackTriangle (completeBoundaryOriginalFiberMap K n h g c (nodeι K n i ≫ q))
      (pullback.fst (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K))
      (completeBoundaryNodeMap K n h g i)
      (completeBoundaryOriginalFiberMap_fst K n h g c (nodeι K n i ≫ q))
      (completeMarkingDescendedTestIso K n h s (Over.mk (g ≫ completeClosedBase K)))
      (completeBoundaryFiberNodeLineIso K n h g c i)
      (completeDescendedNodeLineIso K n h s g i) :=
  (completeBoundaryFiberNodeLineIso_triangle K n h g c i).sourceIso
    ((lineBundleForget _).mapIso (completeMarkingDescentIso K n h s)).symm

end FLT.Mazur.PolygonInfinitesimalStages
