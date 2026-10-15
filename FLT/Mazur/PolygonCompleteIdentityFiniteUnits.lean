/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteCoordinates
public import FLT.Mazur.LaurentPairUnitSections
public import FLT.Mazur.SchemeMonoidUnitEvaluation

/-!
# Actual left and right unit equations for original finite Laurent multiplication

These equations concern the constructed original multiplication on full
nonreduced Laurent schemes, not only its closed points or residue coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPairUnitSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "e" => completeIdentityStageTorus K n h i m
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (A) (A)[T;T⁻¹]))
local notation "s" => (b) ≫ baseToSeries K m

/-- The finite Laurent inclusion is a monomorphism over the original complete base. -/
instance completeIdentityStageTorus_mono : Mono (e) :=
  (completeIdentityFiniteParameter_isPullback K n h i m).mono_fst_of_mono

/-- The first unit slice of actual original multiplication is the original second input. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_firstUnit :
    firstUnit (A) ≫ completeIdentityFiniteOriginalMul K n h i m = (e) := by
  have he := (completeIdentityFiniteParameter_isPullback K n h i m).w
  have hu : (η[(G).X]).left ≫ (G).X.hom = 𝟙 (Spec (.of (PowerSeries K))) :=
    (η[(G).X]).w
  have hc : ((s) ≫ (η[(G).X]).left) ≫ (G).X.hom = (e) ≫ (G).X.hom := by
    rw [Category.assoc, hu, Category.comp_id, he]
  have hp : firstUnit (A) ≫ completeIdentityFinitePair K n h i m =
      pullback.lift ((s) ≫ (η[(G).X]).left) (e) hc := by
    apply pullback.hom_ext
    · rw [Category.assoc, completeIdentityFinitePair_fst, firstUnit_fst_assoc,
        completeIdentityStageTorus_one, pullback.lift_fst,
        completePointOriginalBaseGroup_identity, Category.assoc]
    · rw [Category.assoc, completeIdentityFinitePair_snd, firstUnit_snd_assoc,
        pullback.lift_snd]
  rw [completeIdentityFiniteOriginalMul, ← Category.assoc, hp]
  exact SchemeMonoidUnitEvaluation.left_unit (G).X (s) (e) he hc

/-- The second unit slice of actual original multiplication is the original first input. -/
@[reassoc] theorem completeIdentityFiniteOriginalMul_secondUnit :
    secondUnit (A) ≫ completeIdentityFiniteOriginalMul K n h i m = (e) := by
  have he := (completeIdentityFiniteParameter_isPullback K n h i m).w
  have hu : (η[(G).X]).left ≫ (G).X.hom = 𝟙 (Spec (.of (PowerSeries K))) :=
    (η[(G).X]).w
  have hc : (e) ≫ (G).X.hom = ((s) ≫ (η[(G).X]).left) ≫ (G).X.hom := by
    rw [Category.assoc, hu, Category.comp_id, he]
  have hp : secondUnit (A) ≫ completeIdentityFinitePair K n h i m =
      pullback.lift (e) ((s) ≫ (η[(G).X]).left) hc := by
    apply pullback.hom_ext
    · rw [Category.assoc, completeIdentityFinitePair_fst, secondUnit_fst_assoc,
        pullback.lift_fst]
    · rw [Category.assoc, completeIdentityFinitePair_snd, secondUnit_snd_assoc,
        completeIdentityStageTorus_one, pullback.lift_snd,
        completePointOriginalBaseGroup_identity, Category.assoc]
  rw [completeIdentityFiniteOriginalMul, ← Category.assoc, hp]
  exact SchemeMonoidUnitEvaluation.right_unit (G).X (s) (e) he hc

/-- The full coordinate law is normalized at one in its first variable. -/
@[reassoc] theorem completeIdentityFiniteMulCoordinates_firstUnit :
    firstUnit (A) ≫ completeIdentityFiniteMulCoordinates K n h i m = 𝟙 _ := by
  apply (cancel_mono (e)).mp
  rw [Category.assoc, completeIdentityFiniteMulCoordinates_original,
    completeIdentityFiniteOriginalMul_firstUnit, Category.id_comp]

/-- The full coordinate law is normalized at one in its second variable. -/
@[reassoc] theorem completeIdentityFiniteMulCoordinates_secondUnit :
    secondUnit (A) ≫ completeIdentityFiniteMulCoordinates K n h i m = 𝟙 _ := by
  apply (cancel_mono (e)).mp
  rw [Category.assoc, completeIdentityFiniteMulCoordinates_original,
    completeIdentityFiniteOriginalMul_secondUnit, Category.id_comp]

end FLT.Mazur.PolygonInfinitesimalStages
