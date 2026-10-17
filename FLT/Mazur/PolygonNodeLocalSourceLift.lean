/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointNodeLocalization
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Source-node maps extend to the original marking localization

Both source coordinates in the maximal ideal make the original marking
denominator a unit. The extension changes no value in the receiving ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
variable (K : Type) [Field K] (m : ℕ)
variable {D : Type} [CommRing D] [IsLocalRing D]
variable (f : ChartRing (parameter K m) →+* D)
variable (hx : f (leftCoordinate (parameter K m)) ∈ IsLocalRing.maximalIdeal D)
variable (hy : f (rightCoordinate (parameter K m)) ∈ IsLocalRing.maximalIdeal D)
local notation "t" => parameter K m

include hx hy in
/-- The actual source marking denominator is a unit in the full local receiving ring. -/
theorem stageNodeLocalSource_denominator : IsUnit (f (nodeMarkingDenominator (t))) := by
  rw [nodeMarkingDenominator, f.map_mul, f.map_sub, f.map_sub, f.map_one]
  exact (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hx).mul
    (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hy)

/-- Extend the unchanged source map by inverting its original marking denominator. -/
def stageNodeLocalSourceLift : StageNodeLocalization K m →+* D :=
  IsLocalization.Away.lift (nodeMarkingDenominator (t)) (g := f)
    (stageNodeLocalSource_denominator K m f hx hy)

/-- Every original source function has exactly its previous value. -/
theorem stageNodeLocalSourceLift_algebraMap (z : ChartRing (t)) :
    stageNodeLocalSourceLift K m f hx hy
      (algebraMap (ChartRing (t)) (StageNodeLocalization K m) z) = f z :=
  IsLocalization.Away.lift_eq _ _ _

/-- The localized map retains the original source homomorphism on the entire node ring. -/
theorem stageNodeLocalSourceLift_comp :
    (stageNodeLocalSourceLift K m f hx hy).comp
      (algebraMap (ChartRing (t)) (StageNodeLocalization K m)) = f := by
  apply RingHom.ext
  intro z
  exact stageNodeLocalSourceLift_algebraMap K m f hx hy z

end FLT.Mazur.PolygonInfinitesimalStages
