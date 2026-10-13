/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryOriginalRefinement
public import FLT.Mazur.PolygonCompleteBoundaryFiberFrames

/-!
# Original fiber frames commute with complete-family test refinement

The existing complete-family test line, actual fiber normalization and original
component base-change comparison form a commuting square. The node square uses
the exact unit frame. No compatibility of the two translation choices is needed.
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
  {T U : Scheme} (g : T ⟶ Spec (.of K)) (k : U ⟶ T)
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

open SchemePicard

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
  (d : 𝟙_ (Over U) ⟶ (Over.pullback (k ≫ g)).obj (G K n)) (i : Fin n)
local notation "κ" => completeBoundaryTestMap K g k
local notation "r" => relativeTotalMap (exactVeroneseProjToBase K n h) (κ)
local notation "ν" => completeBoundaryOriginalFiberMap K n h g c (componentι K n i ≫ p)
local notation "ν'" => completeBoundaryOriginalFiberMap K n h (k ≫ g) d (componentι K n i ≫ p)
local notation "η" => completeBoundaryOriginalFiberMap K n h g c (nodeι K n i ≫ q)
local notation "η'" => completeBoundaryOriginalFiberMap K n h (k ≫ g) d (nodeι K n i ≫ q)
local notation "δP" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g))
  (component K))
local notation "πP" => pullback.fst
  (Over.hom (CategoryTheory.Functor.obj (Over.pullback g) (component K))) k
local notation "δQ" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g))
  (point K))
local notation "πQ" => pullback.fst
  (Over.hom (CategoryTheory.Functor.obj (Over.pullback g) (point K))) k
local notation "J" => Scheme.IdealSheafData.comap
  (Scheme.Hom.ker (PolygonMarkedSections.sectionMap K n p 1 i))
  (Over.Hom.left (componentι K n i ≫ p))
local notation "hJ" => normalizationIdeal_relativeCartier K n hn p q hp 1 i i

/-- Refine the actual fiber line and then recover the original normalization line. -/
def completeBoundaryNormalizationTestLineIso :
    (Scheme.Modules.pullback ((ν') ≫ (r))).obj
      (completeFiberMarkingLine K n h (g ≫ completeClosedBase K)) ≅
        normalizationMarkingLine K n hn p q hp 1 i i (k ≫ g) :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (completeMarkingTestLineIso K n h (κ)) ≪≫
      completeBoundaryFiberNormalizationLineIso K n h (k ≫ g) d i

/-- The actual test-to-normalization comparison preserves the original marking section. -/
theorem completeBoundaryNormalizationTestLineIso_section :
    DivisorLineSectionCompatible ((ν') ≫ (r))
      (completeFiberMarkingDivisor_relativeCartier K n h (g ≫ completeClosedBase K)).1
      (relativeCartierBaseChange (component K).hom (k ≫ g) _ (hJ)).1
      (completeBoundaryNormalizationTestLineIso K n h g k d i) :=
  (completeMarkingTestLineIso_section K n h (κ)).comp
    (completeBoundaryFiberNormalizationLineIso_section K n h (k ≫ g) d i)

/-- Arbitrary complete-family test refinement preserves the original normalization frame. -/
theorem completeBoundaryFiberNormalizationLineIso_refinement_square :
    LinePullbackSquare (δP) ((ν') ≫ (r)) (πP) (ν)
      (completeBoundaryFiberNormalization_refinement K n h g k c d i)
      (completeBoundaryNormalizationTestLineIso K n h g k d i)
      (relativeCartierBaseChangeCompositionIso (component K) g k (J) (hJ))
      (completeBoundaryFiberNormalizationLineIso K n h g c i)
      (relativeCartierDivisorPullbackIso ((Over.pullback g).obj (component K)).hom k _
        (relativeCartierBaseChange (component K).hom g _ (hJ))) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeBoundaryNormalizationTestLineIso_section K n h g k d i)
    (relativeCartierBaseChangeCompositionIso_section (component K) g k (J) (hJ))
    (completeBoundaryFiberNormalizationLineIso_section K n h g c i)
    (relativeCartierDivisorPullbackIso_section ((Over.pullback g).obj (component K)).hom k _
      (relativeCartierBaseChange (component K).hom g _ (hJ)))

/-- Refine the actual fiber line and then recover the original node frame. -/
def completeBoundaryNodeTestLineIso :
    (Scheme.Modules.pullback ((η') ≫ (r))).obj
      (completeFiberMarkingLine K n h (g ≫ completeClosedBase K)) ≅
        divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (completeMarkingTestLineIso K n h (κ)) ≪≫
      completeBoundaryFiberNodeLineIso K n h (k ≫ g) d i

/-- Test-to-node recovery preserves the exact unit section. -/
theorem completeBoundaryNodeTestLineIso_section :
    DivisorLineSectionCompatible ((η') ≫ (r))
      (completeFiberMarkingDivisor_relativeCartier K n h (g ≫ completeClosedBase K)).1
      effectiveCartier_top (completeBoundaryNodeTestLineIso K n h g k d i) :=
  (completeMarkingTestLineIso_section K n h (κ)).comp
    (completeBoundaryFiberNodeLineIso_section K n h (k ≫ g) d i)

/-- Arbitrary complete-family test refinement retains the original unit node frame. -/
theorem completeBoundaryFiberNodeLineIso_refinement_square :
    LinePullbackSquare (δQ) ((η') ≫ (r)) (πQ) (η)
      (completeBoundaryFiberNode_refinement K n h g k c d i)
      (completeBoundaryNodeTestLineIso K n h g k d i) (divisorEmptyLinePullbackIso (δQ))
      (completeBoundaryFiberNodeLineIso K n h g c i) (divisorEmptyLinePullbackIso (πQ)) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeBoundaryNodeTestLineIso_section K n h g k d i)
    (divisorEmptyLinePullbackIso_section (δQ))
    (completeBoundaryFiberNodeLineIso_section K n h g c i)
    (divisorEmptyLinePullbackIso_section (πQ))

end FLT.Mazur.PolygonInfinitesimalStages
