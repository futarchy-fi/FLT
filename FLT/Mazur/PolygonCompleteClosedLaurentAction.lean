/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedParameterReduction
public import FLT.Mazur.PolygonInfinitesimalUniversalNaturality

/-!
# The full original action on every closed Laurent parameter chart

Reducing the original finite inputs identifies the whole closed action with
universal reciprocal scaling and the actual complete rotation. The polygon
input includes its singular points; the Laurent parameter remains variable.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj completeClosedFiberInclusion completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "j" => completeClosedFiberInclusion K n h
local notation "q" => toBase K[T;T⁻¹] (LaurentPolynomial.C (0 : K)) n h
local notation "r" => scalingParameterProjection K 0 n h
local notation "z" => zeroFiberIso K n h

/-- The full closed Laurent polygon maps to each original finite Laurent polygon. -/
def completeClosedLaurentReduction (m : ℕ) :
    scalingParameterFamily K 0 n h ⟶ scalingParameterFamily (Ring K m) (parameter K m) n h :=
  scalingParameterMap (reduction K m).toRingHom (parameter K m) 0
    (reduction_parameter K m) n h

/-- Forgetting the finite parameter recovers the unchanged original closed inclusion. -/
@[reassoc] theorem completeClosedLaurentReduction_original (m : ℕ) :
    completeClosedLaurentReduction K n h m ≫
        scalingParameterProjection (Ring K m) (parameter K m) n h ≫
        originalStageToCompatibleProj K n h m = (r) ≫ (z).inv ≫ (j) := by
  rw [completeClosedLaurentReduction, scalingParameterMap_projection_assoc]
  have he : zeroSpecialization K m n h ≫ originalStageToCompatibleProj K n h m =
      (z).inv ≫ (j) := by
    apply (cancel_epi (z).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc]
    exact specialFiberInclusion_toComplete K n h m
  exact congrArg ((r) ≫ ·) he

/-- The actual closed input in the original smooth-by-whole product on each chart. -/
def completeClosedLaurentInput (i : Fin n) :
    scalingParameterFamily K 0 n h ⟶ ((M) ⊗ (X)).left :=
  completeClosedLaurentReduction K n h 0 ≫
    completeWholeFiniteInput K n h 0 (ZMod.finEquiv n i)

/-- Its first projection is the full original closed smooth Laurent parameter. -/
@[reassoc] theorem completeClosedLaurentInput_fst (i : Fin n) :
    completeClosedLaurentInput K n h i ≫
        (CartesianMonoidalCategory.fst (M) (X)).left =
      (q) ≫ completeClosedFiniteChart K n h i ≫ completeClosedSmoothInclusion K n h := by
  rw [completeClosedLaurentInput, completeWholeFiniteInput, Category.assoc, Category.assoc,
    ← Over.comp_left, CartesianMonoidalCategory.tensorHom_fst, Over.comp_left]
  change _ ≫ completeIdentityFiniteInput K n h 0 0 ≫
    pullback.fst _ _ ≫ _ = _
  rw [completeIdentityFiniteInput_fst_assoc, ← Category.assoc,
    completeClosedLaurentReduction, scalingParameterMap_base, Category.assoc]
  change (q) ≫ completeClosedParameterReduction K 0 ≫
    (completeFiniteParameter K n h 0 (ZMod.finEquiv n i)).left = _
  rw [completeClosedParameterReduction_parameter]

/-- Its second projection is the whole closed polygon, with all nodes retained. -/
@[reassoc] theorem completeClosedLaurentInput_snd (i : Fin n) :
    completeClosedLaurentInput K n h i ≫
        (CartesianMonoidalCategory.snd (M) (X)).left = (r) ≫ (z).inv ≫ (j) := by
  rw [completeClosedLaurentInput, completeWholeFiniteInput, Category.assoc, Category.assoc,
    ← Over.comp_left, CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
  change _ ≫ completeIdentityFiniteInput K n h 0 0 ≫ pullback.snd _ _ = _
  rw [completeIdentityFiniteInput_snd, completeClosedLaurentReduction_original]

/-- The full original action on each closed parameter chart is the original universal scaling. -/
@[reassoc] theorem completeWholeAction_closedLaurent (i : Fin n) :
    completeClosedLaurentInput K n h i ≫ (completeWholeAction K n h).left =
      universalScaling K 0 n h ≫ (z).inv ≫ (j) ≫
        completeRotation K n h (ZMod.finEquiv n i) := by
  rw [completeClosedLaurentInput, Category.assoc, completeWholeAction_finite_rotated,
    completeIdentityFiniteScaling, ← Category.assoc,
    completeClosedLaurentReduction, scalingParameterMap_universalScaling_assoc]
  have he : zeroSpecialization K 0 n h ≫ originalStageToCompatibleProj K n h 0 =
      (z).inv ≫ (j) := by
    apply (cancel_epi (z).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc]
    exact specialFiberInclusion_toComplete K n h 0
  change universalScaling K 0 n h ≫
    (zeroSpecialization K 0 n h ≫ originalStageToCompatibleProj K n h 0) ≫ _ = _
  rw [he, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
