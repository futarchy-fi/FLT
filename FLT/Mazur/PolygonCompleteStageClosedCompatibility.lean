/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiber
public import FLT.Mazur.PolygonStageRetainedNaturality
public import FLT.Mazur.PolygonParameterProjectionComposition

/-!
# Every original finite stage retains the same closed polygon inclusion

The concrete reduction maps commute with the original stage restrictions.
Consequently each finite-stage realization has literally the same closed
polygon map into the complete family, not merely an isomorphic closed fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

omit [NeZero n] in
/-- The actual closed-polygon inclusions commute with each original adjacent restriction. -/
@[reassoc] theorem specialFiberInclusion_stageRestriction (m : ℕ) :
    specialFiberInclusion K m n h ≫ stageRestriction K m n h =
      specialFiberInclusion K (m + 1) n h := by
  have he : (reduction K m).toRingHom.comp (restriction K m).toRingHom =
      (reduction K (m + 1)).toRingHom :=
    congrArg AlgHom.toRingHom (reduction_restriction K m)
  simp only [specialFiberInclusion, zeroSpecialization, stageRestriction, Category.assoc,
    PolygonInfinitesimal.parameterProjection_comp, he]

/-- Every finite stage has the unchanged original closed inclusion in the complete family. -/
@[reassoc] theorem specialFiberInclusion_toComplete (m : ℕ) :
    specialFiberInclusion K m n h ≫ originalStageToCompatibleProj K n h m =
      completeClosedFiberInclusion K n h := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : stageRestriction K m n h ≫ originalStageToCompatibleProj K n h (m + 1) =
        originalStageToCompatibleProj K n h m := by
      simpa only [stageSystem, Functor.ofSequence_map_homOfLE_succ] using
        originalStageToCompatibleProj_naturality K n h (homOfLE (Nat.le_succ m))
    rw [← specialFiberInclusion_stageRestriction K n h m, Category.assoc, he, ih]

/-- An original complete-family open has exactly its original closed preimage at every stage. -/
theorem specialFiber_preimage_originalStage (m : ℕ)
    (U : (exactVeroneseProj K n h).Opens) :
    specialFiberInclusion K m n h ⁻¹ᵁ (originalStageToCompatibleProj K n h m ⁻¹ᵁ U) =
      completeClosedFiberInclusion K n h ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, specialFiberInclusion_toComplete]

end FLT.Mazur.PolygonInfinitesimalStages
