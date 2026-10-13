/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryOriginalFiber
public import FLT.Mazur.PolygonCompleteBoundaryFrameRefinement
public import FLT.Mazur.PolygonCompleteMarkingTestLine

/-!
# Actual complete-fiber refinement preserves original boundary maps

The original normalization and node maps commute with the existing total-space
map of complete-family tests. The two varying translations may be chosen
independently: original fiber recovery eliminates that choice on both sides.
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

/-- A parameter refinement is an actual morphism of tests of the original complete family. -/
def completeBoundaryTestMap :
    Over.mk ((k ≫ g) ≫ completeClosedBase K) ⟶ Over.mk (g ≫ completeClosedBase K) :=
  Over.homMk k (Category.assoc k g (completeClosedBase K)).symm

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
  (d : 𝟙_ (Over U) ⟶ (Over.pullback (k ≫ g)).obj (G K n))
  {X : Over (Spec (.of K))}
local notation "δ" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g)) X)
local notation "π" => pullback.fst
  (Over.hom (CategoryTheory.Functor.obj (Over.pullback g) X)) k
local notation "r" => relativeTotalMap (exactVeroneseProjToBase K n h)
  (completeBoundaryTestMap K g k)

/-- Original boundary maps commute with actual complete-fiber refinement for any translations. -/
theorem completeBoundaryOriginalFiberMap_refinement (f : X ⟶ C) :
    (δ) ≫ completeBoundaryOriginalFiberMap K n h (k ≫ g) d f ≫ (r) =
      (π) ≫ completeBoundaryOriginalFiberMap K n h g c f := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [relativeTotalMap_fst _ (completeBoundaryTestMap K g k)]
    dsimp only [Over.mk_hom]
    rw [completeBoundaryOriginalFiberMap_fst, completeBoundaryOriginalFiberMap_fst]
    exact completeBoundaryOriginalMap_refinement K n h g k f
  · simp only [Category.assoc]
    rw [relativeTotalMap_snd _ (completeBoundaryTestMap K g k)]
    dsimp only [Over.mk_hom, completeBoundaryTestMap, Over.homMk_left]
    rw [completeBoundaryOriginalFiberMap_snd_assoc, completeBoundaryOriginalFiberMap_snd]
    rw [← Category.assoc, Over.w]
    exact pullback.condition.symm

/-- The actual normalization maps retain both the refinement and the complete-family tests. -/
theorem completeBoundaryFiberNormalization_refinement (i : Fin n) :
    ((Over.pullbackComp k g).inv.app (component K)).left ≫
        completeBoundaryOriginalFiberMap K n h (k ≫ g) d (componentι K n i ≫ p) ≫ (r) =
      pullback.fst ((Over.pullback g).obj (component K)).hom k ≫
        completeBoundaryOriginalFiberMap K n h g c (componentι K n i ≫ p) :=
  completeBoundaryOriginalFiberMap_refinement K n h g k c d _

/-- The actual node maps retain the same refinement of complete-family tests. -/
theorem completeBoundaryFiberNode_refinement (i : Fin n) :
    ((Over.pullbackComp k g).inv.app (point K)).left ≫
        completeBoundaryOriginalFiberMap K n h (k ≫ g) d (nodeι K n i ≫ q) ≫ (r) =
      pullback.fst ((Over.pullback g).obj (point K)).hom k ≫
        completeBoundaryOriginalFiberMap K n h g c (nodeι K n i ≫ q) :=
  completeBoundaryOriginalFiberMap_refinement K n h g k c d _

end FLT.Mazur.PolygonInfinitesimalStages
