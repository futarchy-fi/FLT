/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionInputRotation
public import FLT.Mazur.PolygonCompleteIdentityFiniteScaling
public import FLT.Mazur.PolygonCompleteStageRotation

/-!
# Rotation of the full original finite input and scaling

The complete input rotation restricts to the original cyclic rotation of
the variable-parameter polygon. Universal scaling commutes with that rotation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "r" => rotation (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h b
local notation "v" => scalingParameterProjection (A) (t) n h
local notation "p" => originalStageToCompatibleProj K n h m
local notation "f" => completeIdentityFiniteInput K n h 0 m

/-- Forgetting the variable unit retains the original cyclic rotation. -/
@[reassoc] theorem completeIdentityFiniteProjection_rotation :
    (r) ≫ (v) = (v) ≫ stageRotation K n h m b :=
  rotation_parameterProjection LaurentPolynomial.C (t) (LaurentPolynomial.C (t)) rfl n h b

/-- The complete whole-input rotation restricts to the exact original finite rotation. -/
@[reassoc] theorem completeIdentityFiniteInput_rotation :
    (r) ≫ (f) = (f) ≫ completeIdentityActionInputRotation K n h b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityFiniteInput_fst,
      completeIdentityActionInputRotation_fst, rotation_toBase_assoc]
  · simp only [Category.assoc, completeIdentityFiniteInput_snd,
      completeIdentityActionInputRotation_snd, completeIdentityFiniteInput_snd_assoc,
      originalStageToCompatibleProj_rotation,
      completeIdentityFiniteProjection_rotation_assoc]

/-- Universal reciprocal scaling commutes with the same original finite rotation. -/
@[reassoc] theorem completeIdentityUniversalScaling_rotation :
    (r) ≫ universalScaling (A) (t) n h =
      universalScaling (A) (t) n h ≫ stageRotation K n h m b := by
  rw [universalScaling, ← Category.assoc, ← scaling_rotation, Category.assoc,
    completeIdentityFiniteProjection_rotation, Category.assoc]

/-- The complete-valued finite scaling retains the original whole-family rotation. -/
@[reassoc] theorem completeIdentityFiniteScaling_rotation :
    (r) ≫ completeIdentityFiniteScaling K n h m =
      completeIdentityFiniteScaling K n h m ≫ completeRotation K n h b := by
  rw [completeIdentityFiniteScaling, completeIdentityUniversalScaling_rotation_assoc,
    Category.assoc, originalStageToCompatibleProj_rotation]

end FLT.Mazur.PolygonInfinitesimalStages
