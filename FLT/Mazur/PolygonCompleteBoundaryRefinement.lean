/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTranslation
public import FLT.Mazur.PolygonParameterProductBaseChange

/-!
# Arbitrary refinement of the original smoothing-boundary recovery

The original iterated base-change chart intertwines the recovery morphisms
into the complete smoothing. The resulting square preserves the full moved
product, its actual positive line, and its canonical marking section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T U : Scheme} (g : T ⟶ Spec (.of K)) (k : U ⟶ T)
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "δ" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g)) C)
local notation "π" => pullback.fst (Over.hom (CategoryTheory.Functor.obj (Over.pullback g) C)) k
local notation "c'" => parameterBaseChange K n g k c

/-- The actual refinement chart commutes with recovery into the original complete family. -/
theorem completeMovedBoundaryMap_refinement :
    (δ) ≫ completeMovedBoundaryMap K n h (k ≫ g) (c') =
      (π) ≫ completeMovedBoundaryMap K n h g c := by
  have ht := congrArg Over.Hom.left (translationIso_baseChange_inv K n hn p q hp g k c)
  dsimp only [Over.comp_left] at ht
  simp only [completeMovedBoundaryMap, completeBoundaryParameterMap]
  rw [← Category.assoc (δ), ← ht, Category.assoc, OverPullbackSection.comp_inv_fst_assoc]
  simp only [Over.pullback_map_left, pullback.lift_fst_assoc, Category.assoc]

/-- Refinement preserves the whole smoothing recovery square on the actual moved product lines. -/
theorem completeMovedBoundaryLineIso_refinement_square :
    LinePullbackSquare (δ) (completeMovedBoundaryMap K n h (k ≫ g) (c'))
      (π) (completeMovedBoundaryMap K n h g c)
      (completeMovedBoundaryMap_refinement K n h g k c)
      (completeMovedBoundaryLineIso K n h (k ≫ g) (c'))
      (movedProductMarkingBaseChangeLineIso K n hn p q hp g k c (fun _ ↦ 1))
      (completeMovedBoundaryLineIso K n h g c)
      (relativeCartierDivisorPullbackIso ((Over.pullback g).obj C).hom k _
        (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1))) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (completeMovedBoundaryLineIso_section K n h (k ≫ g) (c'))
    (movedProductMarkingBaseChangeLineIso_section K n hn p q hp g k c (fun _ ↦ 1))
    (completeMovedBoundaryLineIso_section K n h g c)
    (relativeCartierDivisorPullbackIso_section ((Over.pullback g).obj C).hom k _
      (movedProductMarkingIdeal_cartier K n hn p q hp g c (fun _ ↦ 1)))

end FLT.Mazur.PolygonInfinitesimalStages
