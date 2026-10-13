/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryCartesian

/-!
# Original labels on the complete family's translated boundary

Every original all-one polygon section is the corresponding complete marking.
After arbitrary parameter change and varying translation, the actual fiber
isomorphism retains those same labeled sections, not only their product ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction PolygonMarkedSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
  originalStageToCompatibleProj completeBaseMarking
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- Each original all-one polygon label maps to the matching complete smoothing section. -/
@[reassoc] theorem completeBoundaryInclusion_marking (i : Fin n) :
    sectionMap K n p 1 i ≫ completeBoundaryInclusion K n h =
      completeClosedBase K ≫ completeBaseMarking K n h i := by
  rw [completeBoundaryInclusion, specialFiberInclusion, Category.assoc,
    PolygonInfinitesimal.boundarySection_zeroFiberIso_assoc,
    marking_zeroSpecialization_assoc,
    ← baseToSeries_completeBaseMarking, ← Category.assoc, reductionBase_toSeries]

variable {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "τ" => translationIso K n hn p q hp g c

/-- The original labeled section after actual parameter change and varying translation. -/
def completeMovedBoundaryMarking (i : Fin n) : T ⟶ ((Over.pullback g).obj C).left :=
  sectionBaseChange (C).hom g (sectionMap K n p 1 i) (section_base K n p 1 i) ≫
    (τ).hom.left

/-- Each moved label retains the corresponding original complete marking. -/
@[reassoc] theorem completeMovedBoundaryMarking_toComplete (i : Fin n) :
    completeMovedBoundaryMarking K n h g c i ≫ completeMovedBoundaryMap K n h g c =
      (g ≫ completeClosedBase K) ≫ completeBaseMarking K n h i := by
  rw [completeMovedBoundaryMarking, Category.assoc, translation_completeMovedBoundaryMap,
    completeBoundaryParameterMap, ← Category.assoc]
  simp only [sectionBaseChange, pullback.lift_fst, Category.assoc,
    completeBoundaryInclusion_marking]

/-- The moved original label is still a section of the actual parameter projection. -/
@[reassoc] theorem completeMovedBoundaryMarking_toBase (i : Fin n) :
    completeMovedBoundaryMarking K n h g c i ≫ ((Over.pullback g).obj C).hom = 𝟙 T := by
  rw [completeMovedBoundaryMarking, Category.assoc, Over.w]
  exact sectionBaseChange_snd _ _ _ _

/-- The complete-family fiber comparison preserves each original label individually. -/
@[reassoc] theorem completeMovedBoundaryFiberIso_marking (i : Fin n) :
    completeMovedBoundaryMarking K n h g c i ≫ (completeMovedBoundaryFiberIso K n h g c).hom =
      completeFiberMarking K n h (g ≫ completeClosedBase K) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeMovedBoundaryFiberIso_fst,
      completeMovedBoundaryMarking_toComplete, completeFiberMarking_fst]
  · rw [Category.assoc, completeMovedBoundaryFiberIso_snd,
      completeMovedBoundaryMarking_toBase, completeFiberMarking_snd]

end FLT.Mazur.PolygonInfinitesimalStages
