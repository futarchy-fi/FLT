/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryOriginalFiber
public import FLT.Mazur.PolygonCompleteBoundaryFiberLine

/-!
# Original normalization and node frames of the actual complete-family fiber

The actual fiber's full marking line restricts to the original component line
and unit node frame. These comparisons retain the complete smoothing recovery
triangle and both original branch incidence triangles, including their sections.
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
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (i : Fin n)
local notation "ν" => completeBoundaryOriginalFiberMap K n h g c (componentι K n i ≫ p)
local notation "η" => completeBoundaryOriginalFiberMap K n h g c (nodeι K n i ≫ q)

/-- The actual complete-family fiber recovers the original normalization marking line. -/
def completeBoundaryFiberNormalizationLineIso :
    (Scheme.Modules.pullback (ν)).obj
      (completeFiberMarkingLine K n h (g ≫ completeClosedBase K)) ≅
        normalizationMarkingLine K n hn p q hp 1 i i g :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (completeBoundaryFiberLineIso K n h g c) ≪≫
      movedProductNormalizationLineIso K n hn p q hp g c (fun _ ↦ 1) i

/-- The actual fiber normalization comparison preserves the canonical product section. -/
theorem completeBoundaryFiberNormalizationLineIso_section :
    DivisorLineSectionCompatible (ν)
      (completeFiberMarkingDivisor_relativeCartier K n h (g ≫ completeClosedBase K)).1
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q hp 1 i i)).1
      (completeBoundaryFiberNormalizationLineIso K n h g c i) :=
  (completeBoundaryFiberLineIso_section K n h g c).comp
    (movedProductNormalizationLineIso_section K n hn p q hp g c (fun _ ↦ 1) i)

/-- The actual complete-family fiber recovers the original empty-divisor node frame. -/
def completeBoundaryFiberNodeLineIso :
    (Scheme.Modules.pullback (η)).obj
      (completeFiberMarkingLine K n h (g ≫ completeClosedBase K)) ≅
        divisorLineBundle ⊤ effectiveCartier_top :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (completeBoundaryFiberLineIso K n h g c) ≪≫
      movedProductNodeLineIso K n hn p q hp g c (fun _ ↦ 1) i

/-- The actual fiber node frame preserves the canonical section exactly. -/
theorem completeBoundaryFiberNodeLineIso_section :
    DivisorLineSectionCompatible (η)
      (completeFiberMarkingDivisor_relativeCartier K n h (g ≫ completeClosedBase K)).1
      effectiveCartier_top (completeBoundaryFiberNodeLineIso K n h g c i) :=
  (completeBoundaryFiberLineIso_section K n h g c).comp
    (movedProductNodeLineIso_section K n hn p q hp g c (fun _ ↦ 1) i)

/-- The actual fiber and complete-family normalization comparisons agree exactly. -/
theorem completeBoundaryFiberNormalizationLineIso_triangle :
    LinePullbackTriangle (ν)
      (pullback.fst (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K))
      (completeBoundaryNormalizationMap K n h g i)
      (completeBoundaryOriginalFiberMap_fst K n h g c (componentι K n i ≫ p))
      (completeMarkingLineBaseChangeIso K n h (g ≫ completeClosedBase K))
      (completeBoundaryFiberNormalizationLineIso K n h g c i)
      (completeBoundaryNormalizationLineIso K n h g i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMarkingLineBaseChangeIso_section K n h (g ≫ completeClosedBase K))
    (completeBoundaryFiberNormalizationLineIso_section K n h g c i)
    (completeBoundaryNormalizationLineIso_section K n h g i)

/-- The actual fiber and complete-family node comparisons retain the same unit frame. -/
theorem completeBoundaryFiberNodeLineIso_triangle :
    LinePullbackTriangle (η)
      (pullback.fst (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K))
      (completeBoundaryNodeMap K n h g i)
      (completeBoundaryOriginalFiberMap_fst K n h g c (nodeι K n i ≫ q))
      (completeMarkingLineBaseChangeIso K n h (g ≫ completeClosedBase K))
      (completeBoundaryFiberNodeLineIso K n h g c i)
      (completeBoundaryNodeLineIso K n h g i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMarkingLineBaseChangeIso_section K n h (g ≫ completeClosedBase K))
    (completeBoundaryFiberNodeLineIso_section K n h g c i)
    (completeBoundaryNodeLineIso_section K n h g i)

/-- Both original branches retain the same exact frame of the actual fiber's marking line. -/
theorem completeBoundaryFiberNormalizationLineIso_node (j : Fin n)
    (s : point K ⟶ component K) (w : s ≫ (componentι K n i ≫ p) = nodeι K n j ≫ q) :
    LinePullbackTriangle ((Over.pullback g).map s).left (ν)
      (completeBoundaryOriginalFiberMap K n h g c (nodeι K n j ≫ q))
      (completeBoundaryOriginalFiberMap_node K n h g c i j s w)
      (completeBoundaryFiberNormalizationLineIso K n h g c i)
      (normalizationEndpointLineIso K n hn p q hp g 1 i i j s w)
      (completeBoundaryFiberNodeLineIso K n h g c j) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeBoundaryFiberNormalizationLineIso_section K n h g c i)
    (normalizationEndpointLineIso_section K n hn p q hp g 1 i i j s w)
    (completeBoundaryFiberNodeLineIso_section K n h g c j)

end FLT.Mazur.PolygonInfinitesimalStages
