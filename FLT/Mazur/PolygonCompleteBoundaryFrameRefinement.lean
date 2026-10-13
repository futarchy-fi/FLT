/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryNormalization
public import FLT.Mazur.PolygonCompleteBoundaryNode
public import FLT.Mazur.PolygonParameterProductNormalizationRefinement

/-!
# Arbitrary refinement of the complete smoothing's original frames

The original normalization and node maps into the complete smoothing commute
with the actual iterated base-change chart. The positive component line and
empty node frame give commuting squares preserving their canonical sections.
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


/-- Every original boundary map into the complete family retains the refinement chart. -/
theorem completeBoundaryOriginalMap_refinement {X : Over (Spec (.of K))} (f : X ⟶ C) :
    ((Over.pullbackComp k g).inv.app X).left ≫
        ((Over.pullback (k ≫ g)).map f).left ≫ completeBoundaryParameterMap K n h (k ≫ g) =
      pullback.fst ((Over.pullback g).obj X).hom k ≫
        ((Over.pullback g).map f).left ≫ completeBoundaryParameterMap K n h g := by
  simp only [completeBoundaryParameterMap, Over.pullback_map_left,
    pullback.lift_fst_assoc, Category.assoc]
  rw [OverPullbackSection.comp_inv_fst_assoc]

variable (i : Fin n)
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

/-- The original normalization recovery map commutes with arbitrary parameter refinement. -/
theorem completeBoundaryNormalizationMap_refinement :
    (δP) ≫ completeBoundaryNormalizationMap K n h (k ≫ g) i =
      (πP) ≫ completeBoundaryNormalizationMap K n h g i :=
  completeBoundaryOriginalMap_refinement K n h g k (componentι K n i ≫ p)

/-- The original node recovery map commutes with the same parameter refinement. -/
theorem completeBoundaryNodeMap_refinement :
    (δQ) ≫ completeBoundaryNodeMap K n h (k ≫ g) i =
      (πQ) ≫ completeBoundaryNodeMap K n h g i :=
  completeBoundaryOriginalMap_refinement K n h g k (nodeι K n i ≫ q)

/-- The complete normalization line retains its exact original refinement square. -/
theorem completeBoundaryNormalizationLineIso_refinement_square :
    LinePullbackSquare (δP) (completeBoundaryNormalizationMap K n h (k ≫ g) i)
      (πP) (completeBoundaryNormalizationMap K n h g i)
      (completeBoundaryNormalizationMap_refinement K n h g k i)
      (completeBoundaryNormalizationLineIso K n h (k ≫ g) i)
      (relativeCartierBaseChangeCompositionIso (component K) g k (J) (hJ))
      (completeBoundaryNormalizationLineIso K n h g i)
      (relativeCartierDivisorPullbackIso ((Over.pullback g).obj (component K)).hom k _
        (relativeCartierBaseChange (component K).hom g _ (hJ))) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeBoundaryNormalizationLineIso_section K n h (k ≫ g) i)
    (relativeCartierBaseChangeCompositionIso_section (component K) g k (J) (hJ))
    (completeBoundaryNormalizationLineIso_section K n h g i)
    (relativeCartierDivisorPullbackIso_section ((Over.pullback g).obj (component K)).hom k _
      (relativeCartierBaseChange (component K).hom g _ (hJ)))

/-- The complete node's empty-divisor frame retains its exact original refinement square. -/
theorem completeBoundaryNodeLineIso_refinement_square :
    LinePullbackSquare (δQ) (completeBoundaryNodeMap K n h (k ≫ g) i)
      (πQ) (completeBoundaryNodeMap K n h g i)
      (completeBoundaryNodeMap_refinement K n h g k i)
      (completeBoundaryNodeLineIso K n h (k ≫ g) i) (divisorEmptyLinePullbackIso (δQ))
      (completeBoundaryNodeLineIso K n h g i) (divisorEmptyLinePullbackIso (πQ)) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeBoundaryNodeLineIso_section K n h (k ≫ g) i)
    (divisorEmptyLinePullbackIso_section (δQ))
    (completeBoundaryNodeLineIso_section K n h g i)
    (divisorEmptyLinePullbackIso_section (πQ))

end FLT.Mazur.PolygonInfinitesimalStages
