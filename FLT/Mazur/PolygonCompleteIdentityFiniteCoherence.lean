/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteScaling
public import FLT.Mazur.PolygonInfinitesimalUniversalNaturality

/-!
# Coherence of the actual finite identity inputs and their polygon-valued maps

The Laurent parameter coordinates commute with the original adjacent stages.
The whole input comparisons and the constructed scaling maps therefore form
compatible systems on the original finite thickenings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)

/-- The original full stage realizations retain the specified adjacent family restriction. -/
@[reassoc] theorem completeIdentityStageRestriction_toComplete :
    stageRestriction K m n h ≫ originalStageToCompatibleProj K n h (m + 1) =
      originalStageToCompatibleProj K n h m := by
  simpa only [stageSystem, Functor.ofSequence_map_homOfLE_succ] using
    originalStageToCompatibleProj_naturality K n h (homOfLE (Nat.le_succ m))

/-- The actual full Laurent identity parameters commute with the original coefficient quotient. -/
@[reassoc] theorem completeIdentityStageTorus_restriction :
    Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap
      (restriction K m).toRingHom)) ≫ completeIdentityStageTorus K n h i (m + 1) =
        completeIdentityStageTorus K n h i m := by
  apply (cancel_mono (completePointIdentityOpen K n h i).ι).mp
  rw [Category.assoc, completeIdentityStageTorus_inclusion,
    completeIdentityStageTorus_inclusion, ← Category.assoc]
  have he := (edge_parameter_isPullback (parameter K (m + 1)) n h
    (restriction K m).toRingHom (parameter K m) (restriction_parameter K m) i).w
  change _ = edge (Ring K m) (parameter K m) n h i ≫ stageRestriction K m n h at he
  rw [he, Category.assoc, completeIdentityStageRestriction_toComplete]

/-- The full finite action-input restriction, with its independent Laurent parameter retained. -/
def completeIdentityFiniteRestriction :
    scalingParameterFamily (Ring K m) (parameter K m) n h ⟶
      scalingParameterFamily (Ring K (m + 1)) (parameter K (m + 1)) n h :=
  scalingParameterMap (restriction K m).toRingHom (parameter K (m + 1)) (parameter K m)
    (restriction_parameter K m) n h

/-- The original whole input comparisons are compatible at every adjacent finite order. -/
@[reassoc] theorem completeIdentityFiniteRestriction_input :
    completeIdentityFiniteRestriction K n h m ≫ completeIdentityFiniteInput K n h i (m + 1) =
      completeIdentityFiniteInput K n h i m := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityFiniteInput_fst, completeIdentityFiniteInput_fst,
      completeIdentityFiniteRestriction, scalingParameterMap_base_assoc,
      completeIdentityStageTorus_restriction]
  · rw [Category.assoc, completeIdentityFiniteInput_snd, completeIdentityFiniteInput_snd,
      completeIdentityFiniteRestriction, scalingParameterMap_projection_assoc]
    change _ ≫ stageRestriction K m n h ≫ originalStageToCompatibleProj K n h (m + 1) = _
    rw [completeIdentityStageRestriction_toComplete]

/-- The polygon-valued maps agree on the actual adjacent original input thickenings. -/
@[reassoc] theorem completeIdentityFiniteRestriction_scaling :
    completeIdentityFiniteRestriction K n h m ≫ completeIdentityFiniteScaling K n h (m + 1) =
      completeIdentityFiniteScaling K n h m := by
  rw [completeIdentityFiniteScaling, completeIdentityFiniteRestriction,
    scalingParameterMap_universalScaling_assoc]
  change universalScaling (Ring K m) (parameter K m) n h ≫
      stageRestriction K m n h ≫ originalStageToCompatibleProj K n h (m + 1) = _
  rw [completeIdentityStageRestriction_toComplete]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
