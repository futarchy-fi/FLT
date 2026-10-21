/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentCurveTower

/-!
# Closed smooth factors at arbitrary supplied stages

Surjective support coordinates make every supplied smooth factor closed.
The intrinsic character source retains this closedness under its actual
comparison with the stage pullback source.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (hi : complementaryInverse I t ht ∈ s)

/-- The supplied smooth factor expressed on the intrinsic stage character scheme. -/
def stageCharacterFactor : model (stageBase I t ht n s i) (ZMod n) ⟶
    (stageCurve I t ht n s i hi).group :=
  (stageCharacterIso I t ht n s i).hom ≫ stageFactor I t ht n s i b hb hi

/-- Its whole-curve map is the original stage embedding with its source identified. -/
theorem stageCharacterFactor_inclusion :
    stageCharacterFactor I t ht n s i b hb hi ≫ (stageCurve I t ht n s i hi).inclusion =
      (stageCharacterIso I t ht n s i).hom ≫ stageEmbedding I t ht n s i hi := by
  rw [stageCharacterFactor, Category.assoc, stageFactor_inclusion]

variable (hφ : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
  (canonicalCoordinates I t ht n) s))

include hφ

/-- Closedness of the whole stage embedding forces closedness of its smooth factor. -/
theorem stageFactor_isClosedImmersion :
    IsClosedImmersion (stageFactor I t ht n s i b hb hi).left := by
  let _ : IsClosedImmersion
      ((stageFactor I t ht n s i b hb hi).left ≫
        (stageCurve I t ht n s i hi).inclusion.left) := by
    change IsClosedImmersion
      (stageFactor I t ht n s i b hb hi ≫ (stageCurve I t ht n s i hi).inclusion).left
    rw [stageFactor_inclusion]
    exact stageEmbedding_isClosedImmersion I t ht n s i hi hφ
  exact IsClosedImmersion.of_comp _ (stageCurve I t ht n s i hi).inclusion.left

/-- The actual intrinsic-source inclusion is closed for arbitrary supplied stages. -/
theorem stageCharacterFactor_isClosedImmersion :
    IsClosedImmersion (stageCharacterFactor I t ht n s i b hb hi).left := by
  let _ := stageFactor_isClosedImmersion I t ht n s i b hb hi hφ
  change IsClosedImmersion
    ((stageCharacterIso I t ht n s i).hom.left ≫ (stageFactor I t ht n s i b hb hi).left)
  infer_instance

end FLT.Mazur.OneGonAdicIndependentModel
