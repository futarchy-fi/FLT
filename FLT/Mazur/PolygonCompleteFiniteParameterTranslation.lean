/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteFiniteParameterProduct
public import FLT.Mazur.PolygonCompleteIdentityFiniteInputRotation

/-!
# Original varying translations recover the finite scaling automorphisms

On the actual finite Laurent product, the original smooth parameter acts by
the existing universal reciprocal scaling followed by the original rotation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "M" => completeOriginalSmoothOver K n h
local notation "X" => completeOriginalWholeOver K n h
local notation "T₀" => completeFiniteParameterOver K m
local notation "e" => completeFiniteParameterProductIso K n h m
local notation "g" => completeFiniteParameter K n h m b
local notation "q" => toBase (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h
local notation "r" => scalingParameterProjection (A) (t) n h
local notation "p" => originalStageToCompatibleProj K n h m

/-- The action input in the parameter product is the unchanged original finite input. -/
theorem completeFiniteParameter_actionInput :
    (e).hom ≫ (lift (snd (X) (T₀) ≫ (g)) (fst (X) (T₀))).left =
      completeWholeFiniteInput K n h m b := by
  apply pullback.hom_ext
  · change _ ≫ (fst (M) (X)).left = _ ≫ (fst (M) (X)).left
    rw [Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left,
      completeFiniteParameterProductIso_snd_assoc]
    rw [completeWholeFiniteInput, Category.assoc, ← Over.comp_left, tensorHom_fst,
      Over.comp_left]
    change (q) ≫ _ = completeIdentityFiniteInput K n h 0 m ≫
      pullback.fst (completePointOriginalBaseGroup K n h 0).X.hom
        (exactVeroneseProjToBase K n h) ≫ _
    rw [completeIdentityFiniteInput_fst_assoc]
    rfl
  · change _ ≫ (snd (M) (X)).left = _ ≫ (snd (M) (X)).left
    rw [Category.assoc, ← Over.comp_left, lift_snd,
      completeFiniteParameterProductIso_fst]
    rw [completeWholeFiniteInput, Category.assoc, ← Over.comp_left, tensorHom_snd,
      Category.comp_id]
    exact (completeIdentityFiniteInput_snd K n h 0 m).symm

/-- The existing full finite automorphism for the universal unit and rotation. -/
def completeFiniteScalingRotation :
    scalingParameterFamily (A) (t) n h ⟶ scalingParameterFamily (A) (t) n h :=
  scaling (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (PolygonUniversalScaling.u (R := A)) ≫
    rotation (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h b

/-- Its whole original output is the previously constructed universal scaling and rotation. -/
@[reassoc] theorem completeFiniteScalingRotation_original :
    completeFiniteScalingRotation K n h m b ≫ (r) ≫ (p) =
      completeIdentityFiniteScaling K n h m ≫ completeRotation K n h b := by
  rw [completeFiniteScalingRotation, Category.assoc,
    completeIdentityFiniteProjection_rotation_assoc,
    ← originalStageToCompatibleProj_rotation]
  rfl

/-- The universal finite automorphism leaves its entire Laurent parameter unchanged. -/
@[reassoc] theorem completeFiniteScalingRotation_base :
    completeFiniteScalingRotation K n h m b ≫ (q) = (q) := by
  rw [completeFiniteScalingRotation, Category.assoc, rotation_toBase, scaling_toBase]

/-- The actual product identification intertwines translation and the old finite automorphism. -/
@[reassoc] theorem completeFiniteParameterTranslation :
    (e).hom ≫ (completeParameterTranslation K n h (g)).left =
      completeFiniteScalingRotation K n h m b ≫ (e).hom := by
  apply pullback.hom_ext
  · change _ ≫ (fst (X) (T₀)).left = _ ≫ (fst (X) (T₀)).left
    rw [Category.assoc, ← Over.comp_left, completeParameterTranslation, lift_fst,
      Over.comp_left, ← Category.assoc, completeFiniteParameter_actionInput,
      completeWholeAction_finite_rotated, Category.assoc,
      completeFiniteParameterProductIso_fst, completeFiniteScalingRotation_original]
  · change _ ≫ (snd (X) (T₀)).left = _ ≫ (snd (X) (T₀)).left
    rw [Category.assoc, ← Over.comp_left, completeParameterTranslation_snd,
      completeFiniteParameterProductIso_snd, Category.assoc,
      completeFiniteParameterProductIso_snd, completeFiniteScalingRotation_base]

end FLT.Mazur.PolygonInfinitesimalStages
