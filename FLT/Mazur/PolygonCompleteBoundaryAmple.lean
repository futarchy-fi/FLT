/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryCartesian
public import FLT.Mazur.PolygonParameterProductAmple

/-!
# Smoothing ampleness on the whole varying boundary

The complete smoothing's relative section ampleness pulls back along the
actual cartesian square to the entire moved boundary product. This uses the
whole original polygon and works over every parameter scheme.
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
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- Complete smoothing ampleness recovers on the whole original parameter polygon. -/
theorem completeBoundaryProduct_relativelyAmple :
    RelativelyAmpleLineBundle ((Over.pullback g).obj C).hom
      (productMarkingLine K n hn p q hp g (fun _ ↦ 1)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact ((completeMarkingLine_relativelyAmple K n h).of_isPullback
    (completeBoundaryParameter_isPullback K n h g)).of_iso
      (completeBoundaryParameterLineIso K n h g).symm

/-- The actual cartesian recovery retains ampleness of the full varying translated product. -/
theorem completeMovedBoundaryProduct_relativelyAmple :
    RelativelyAmpleLineBundle ((Over.pullback g).obj C).hom
      (movedProductMarkingLine K n hn p q hp g c (fun _ ↦ 1)) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact ((completeMarkingLine_relativelyAmple K n h).of_isPullback
    (completeMovedBoundary_isPullback K n h g c)).of_iso
      (completeMovedBoundaryLineIso K n h g c).symm

end FLT.Mazur.PolygonInfinitesimalStages
