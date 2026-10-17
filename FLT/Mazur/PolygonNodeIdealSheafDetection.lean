/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeBranchIdealDetection
public import FLT.Mazur.PolygonCyclicCocone
public import FLT.Mazur.AffineIdealCoordinates

/-!
# Full ideal sheaf detection on a node with an unchanged branch

Translate branch ideal detection through the actual spectrum coordinates.
These statements apply to arbitrary ideal sheaves, without radical hypotheses.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonNodeIdealSheafDetection
open PolygonCyclicAtlas PolygonNodeEqualizer BaseAdicThickening
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- Coordinates of restriction to the actual first branch. -/
theorem coordinate_first (I : (PolygonNodeBranches.node K).IdealSheafData) :
    coordinateIdeal (.of (Polynomial K)) (I.comap (firstBranch K)) =
      (coordinateIdeal (.of (A (R := K))) I).map (first (R := K)).toRingHom :=
  coordinateIdeal_comap_specMap I (CommRingCat.ofHom (first (R := K)).toRingHom)

/-- Coordinates of restriction to the actual second branch. -/
theorem coordinate_second (I : (PolygonNodeBranches.node K).IdealSheafData) :
    coordinateIdeal (.of (Polynomial K)) (I.comap (secondBranch K)) =
      (coordinateIdeal (.of (A (R := K))) I).map (second (R := K)).toRingHom :=
  coordinateIdeal_comap_specMap I (CommRingCat.ofHom (second (R := K)).toRingHom)

/-- With zero second restriction, the first detects the entire ideal sheaf. -/
theorem eq_of_second_zero {I J : (PolygonNodeBranches.node K).IdealSheafData}
    (hI : I.comap (secondBranch K) = ⊥) (hJ : J.comap (secondBranch K) = ⊥)
    (he : I.comap (firstBranch K) = J.comap (firstBranch K)) : I = J := by
  apply (coordinateIdealEquiv (.of (A (R := K)))).injective
  change coordinateIdeal _ I = coordinateIdeal _ J
  apply PolygonNodeBranchIdealDetection.eq_of_second_zero (R := K)
  · rw [← coordinate_second K I]
    change coordinateIdeal (.of (Polynomial K)) (I.comap (secondBranch K)) = ⊥
    simp only [hI, coordinateIdeal, Scheme.IdealSheafData.ideal_bot,
      Pi.bot_apply, Ideal.map_bot]
  · rw [← coordinate_second K J]
    change coordinateIdeal (.of (Polynomial K)) (J.comap (secondBranch K)) = ⊥
    simp only [hJ, coordinateIdeal, Scheme.IdealSheafData.ideal_bot,
      Pi.bot_apply, Ideal.map_bot]
  · rw [← coordinate_first K I,
      ← coordinate_first K J]
    exact congrArg (coordinateIdeal (.of (Polynomial K))) he

/-- With zero first restriction, the second detects the entire ideal sheaf. -/
theorem eq_of_first_zero {I J : (PolygonNodeBranches.node K).IdealSheafData}
    (hI : I.comap (firstBranch K) = ⊥) (hJ : J.comap (firstBranch K) = ⊥)
    (he : I.comap (secondBranch K) = J.comap (secondBranch K)) : I = J := by
  apply (coordinateIdealEquiv (.of (A (R := K)))).injective
  change coordinateIdeal _ I = coordinateIdeal _ J
  apply PolygonNodeBranchIdealDetection.eq_of_first_zero (R := K)
  · rw [← coordinate_first K I]
    change coordinateIdeal (.of (Polynomial K)) (I.comap (firstBranch K)) = ⊥
    simp only [hI, coordinateIdeal, Scheme.IdealSheafData.ideal_bot,
      Pi.bot_apply, Ideal.map_bot]
  · rw [← coordinate_first K J]
    change coordinateIdeal (.of (Polynomial K)) (J.comap (firstBranch K)) = ⊥
    simp only [hJ, coordinateIdeal, Scheme.IdealSheafData.ideal_bot,
      Pi.bot_apply, Ideal.map_bot]
  · rw [← coordinate_second K I,
      ← coordinate_second K J]
    exact congrArg (coordinateIdeal (.of (Polynomial K))) he

/-- Zero on both full branches means zero on the whole nodal chart. -/
theorem eq_bot {I : (PolygonNodeBranches.node K).IdealSheafData}
    (h₁ : I.comap (firstBranch K) = ⊥) (h₂ : I.comap (secondBranch K) = ⊥) : I = ⊥ := by
  apply eq_of_second_zero K h₂ (Scheme.IdealSheafData.comap_bot _)
  simpa only [Scheme.IdealSheafData.comap_bot] using h₁

end FLT.Mazur.PolygonNodeIdealSheafDetection
