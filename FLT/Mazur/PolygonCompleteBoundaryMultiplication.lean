/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTranslation

/-!
# Multiplication coherence of smoothing recovery on the boundary

A second varying translation preserves recovery into the original smoothing.
The full moved product's multiplication comparison commutes with the original
smoothing-line recovery, including the canonical sections and all tensor degrees.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c d : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- Successive translation retains the original complete-family recovery morphism. -/
theorem completeMovedBoundaryMap_mul :
    (translationIso K n hn p q hp g d).hom.left ≫
      completeMovedBoundaryMap K n h g (d * c) = completeMovedBoundaryMap K n h g c := by
  let e := (Over.forget T).mapIso (translationIso K n hn p q hp g c)
  apply (cancel_epi e.hom).mp
  dsimp only [e, Functor.mapIso_hom, Over.forget_map]
  rw [← Category.assoc, translationIso_mul_hom,
    translation_completeMovedBoundaryMap, translation_completeMovedBoundaryMap]

/-- The whole-product multiplication comparison commutes with complete smoothing recovery. -/
theorem completeMovedBoundaryLineIso_mul_triangle :
    LinePullbackTriangle (translationIso K n hn p q hp g d).hom.left
      (completeMovedBoundaryMap K n h g (d * c)) (completeMovedBoundaryMap K n h g c)
      (completeMovedBoundaryMap_mul K n h g c d)
      (completeMovedBoundaryLineIso K n h g (d * c))
      (movedProductMarkingMulLineIso K n hn p q hp g c d (fun _ ↦ 1))
      (completeMovedBoundaryLineIso K n h g c) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMovedBoundaryLineIso_section K n h g (d * c))
    (movedProductMarkingMulLineIso_section K n hn p q hp g c d (fun _ ↦ 1))
    (completeMovedBoundaryLineIso_section K n h g c)

/-- Every tensor degree keeps the actual multiplication triangle with the smoothing. -/
theorem completeMovedBoundaryLineIso_mul_power_triangle (r : ℕ) :
    LinePullbackTriangle (translationIso K n hn p q hp g d).hom.left
      (completeMovedBoundaryMap K n h g (d * c)) (completeMovedBoundaryMap K n h g c)
      (completeMovedBoundaryMap_mul K n h g c d)
      (tensorPowerPullbackComparison _ (completeMovedBoundaryLineIso K n h g (d * c)) r)
      (tensorPowerPullbackComparison _
        (movedProductMarkingMulLineIso K n hn p q hp g c d (fun _ ↦ 1)) r)
      (tensorPowerPullbackComparison _ (completeMovedBoundaryLineIso K n h g c) r) :=
  (completeMovedBoundaryLineIso_mul_triangle K n h g c d).tensorPower r

end FLT.Mazur.PolygonInfinitesimalStages
