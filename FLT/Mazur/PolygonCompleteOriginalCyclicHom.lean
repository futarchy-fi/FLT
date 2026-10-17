/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGeneralizedCurve
public import FLT.Mazur.PolygonCompleteSmoothGroupRotations
public import FLT.Mazur.RelativeCyclicSubgroup

/-!
# The original cyclic marking in the complete generalized curve

The existing global cyclic sections give a faithful homomorphism into the
constructed full smooth group. Its whole-curve sections retain every old label.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K n h

/-- The unchanged cyclic labels form a homomorphism into the full smooth group. -/
def completeOriginalCyclicPointHom :
    Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ (E).group) where
  toFun b := completeOriginalSmoothCyclicPoint K n h b.toAdd
  map_one' := completeOriginalSmoothCyclicPoint_zero K n h
  map_mul' b c := completeOriginalSmoothCyclicPoint_add K n h b.toAdd c.toAdd

/-- Every whole-curve value is the unchanged original marked section. -/
theorem completeOriginalCyclicPointHom_curve (b : Multiplicative (ZMod n)) :
    (completeOriginalCyclicPointHom K n h b ≫ (E).inclusion).left =
      completeBaseMarking K n h ((ZMod.finEquiv n).symm b.toAdd) := by
  rw [completeGeneralizedCurve_inclusion]
  change (completeOriginalSmoothCyclicPoint K n h b.toAdd).left ≫
    (exactVeroneseProjToBase K n h).smoothLocus.ι = _
  rw [completeOriginalSmoothCyclicPoint_inclusion]
  simp only [PolygonPinching.rotateIndex, map_zero, zero_add]

/-- The original group labels stay distinct over every nonempty test scheme. -/
theorem completeOriginalCyclicPointHom_distinct :
    UniversallyDistinctSections.UniversallyDistinct
      (fun i : ZMod n ↦ completeOriginalCyclicPointHom K n h (.ofAdd i)) := by
  intro V g hV a b he
  obtain ⟨x⟩ := hV
  by_contra hab
  have hij : (ZMod.finEquiv n).symm a ≠ (ZMod.finEquiv n).symm b :=
    fun hi ↦ hab ((ZMod.finEquiv n).symm.injective hi)
  have hh := congrArg (fun z ↦ (z ≫ (E).inclusion).left) he
  change g.left ≫ (completeOriginalCyclicPointHom K n h (.ofAdd a) ≫ (E).inclusion).left =
    g.left ≫ (completeOriginalCyclicPointHom K n h (.ofAdd b) ≫ (E).inclusion).left at hh
  rw [completeOriginalCyclicPointHom_curve, completeOriginalCyclicPointHom_curve] at hh
  have hx := congrArg (fun z : V.left ⟶ (E).curve.left ↦ z x) hh
  exact Set.disjoint_left.mp (completeBaseMarkings_pairwise K n h hij)
    ⟨g.left x, rfl⟩ ⟨g.left x, hx.symm⟩

end FLT.Mazur.PolygonInfinitesimalStages
