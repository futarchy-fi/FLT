/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryCartesian
public import FLT.Mazur.PolygonCompleteBoundaryBranches

/-!
# Original boundary maps inside the actual complete-family fiber

Translate any original boundary map and then use the cartesian comparison.
The resulting map into the actual complete-family fiber is independent of
that translation and preserves original normalization-to-node incidence.
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

variable {X : Over (Spec (.of K))}

/-- Recover an original boundary map inside the actual fiber through the moved polygon. -/
def completeBoundaryOriginalFiberMap
    (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (f : X ⟶ C) :
    ((Over.pullback g).obj X).left ⟶
      pullback (exactVeroneseProjToBase K n h) (g ≫ completeClosedBase K) :=
  (((Over.pullback g).map f).left ≫ (translationIso K n hn p q hp g c).hom.left) ≫
    (completeMovedBoundaryFiberIso K n h g c).hom

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))

/-- The actual fiber map retains the original recovery into the complete smoothing. -/
@[reassoc] theorem completeBoundaryOriginalFiberMap_fst (f : X ⟶ C) :
    completeBoundaryOriginalFiberMap K n h g c f ≫ pullback.fst _ _ =
      ((Over.pullback g).map f).left ≫ completeBoundaryParameterMap K n h g := by
  rw [completeBoundaryOriginalFiberMap, Category.assoc,
    completeMovedBoundaryFiberIso_fst, Category.assoc, translation_completeMovedBoundaryMap]

/-- The actual fiber map retains the original parameter projection. -/
@[reassoc] theorem completeBoundaryOriginalFiberMap_snd (f : X ⟶ C) :
    completeBoundaryOriginalFiberMap K n h g c f ≫ pullback.snd _ _ =
      ((Over.pullback g).obj X).hom := by
  rw [completeBoundaryOriginalFiberMap, Category.assoc,
    completeMovedBoundaryFiberIso_snd, Category.assoc, Over.w, Over.w]

/-- The actual original fiber map is independent of the chosen varying translation. -/
theorem completeBoundaryOriginalFiberMap_independent (f : X ⟶ C)
    (d : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) :
    completeBoundaryOriginalFiberMap K n h g c f =
      completeBoundaryOriginalFiberMap K n h g d f := by
  apply pullback.hom_ext
  · rw [completeBoundaryOriginalFiberMap_fst, completeBoundaryOriginalFiberMap_fst]
  · rw [completeBoundaryOriginalFiberMap_snd, completeBoundaryOriginalFiberMap_snd]

/-- Original incidence maps are retained in the actual complete-family fiber. -/
@[reassoc] theorem completeBoundaryOriginalFiberMap_comp (f : X ⟶ C)
    {Y : Over (Spec (.of K))} (v : Y ⟶ X) :
    ((Over.pullback g).map v).left ≫ completeBoundaryOriginalFiberMap K n h g c f =
      completeBoundaryOriginalFiberMap K n h g c (v ≫ f) := by
  simp only [completeBoundaryOriginalFiberMap, Functor.map_comp, Over.comp_left, Category.assoc]

/-- Both original normalization branches meet the same node in the actual complete fiber. -/
@[reassoc] theorem completeBoundaryOriginalFiberMap_node
    (i j : Fin n) (s : point K ⟶ component K)
    (w : s ≫ (componentι K n i ≫ p) = nodeι K n j ≫ q) :
    ((Over.pullback g).map s).left ≫
        completeBoundaryOriginalFiberMap K n h g c (componentι K n i ≫ p) =
      completeBoundaryOriginalFiberMap K n h g c (nodeι K n j ≫ q) := by
  rw [completeBoundaryOriginalFiberMap_comp, w]

end FLT.Mazur.PolygonInfinitesimalStages
