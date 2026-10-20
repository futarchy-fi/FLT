/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicRecoveredSmoothFactor

/-!
# Finite coefficient descent of the actual canonical smooth factor

The fixed finite character source and the genuine one-gon model admit a
finite coefficient enlargement on which the canonical smooth factor descends.
Both its full cubic composite and its complete-base recovery are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The original smooth factor and its original whole-cubic equation descend together. -/
theorem exists_algebraicSmoothStage :
    ∃ (i : (CoefficientStage (algebraicBase I t ht n))ᵒᵖ)
      (b : (coefficientModelDiagram (algebraicBase I t ht n)
        (algebraicCarrier I t ht n).hom).obj i ⟶
          (integralSmoothOpen (equation (algebraicParameter I t ht n))).toScheme),
      (coefficientModelCone (algebraicBase I t ht n)
        (algebraicCarrier I t ht n).hom).π.app i ≫ b = recoveredSmoothFactor I t ht n ∧
      b ≫ integralSmoothStructure (equation (algebraicParameter I t ht n)) =
        (coefficientModelToInitial (algebraicBase I t ht n)
          (algebraicCarrier I t ht n).hom).app i ≫ (algebraicCarrier I t ht n).hom ∧
      b ≫ (integralSmoothOpen (equation (algebraicParameter I t ht n))).ι =
        (coefficientModelToInitial (algebraicBase I t ht n)
          (algebraicCarrier I t ht n).hom).app i ≫ algebraicEmbedding I t ht n := by
  let _ := (algebraicCarrier_degree I t ht n).1
  exact exists_coefficient_factorization (algebraicBase I t ht n)
    (algebraicCarrier I t ht n).hom
    (integralSmoothStructure (equation (algebraicParameter I t ht n)))
    (algebraicCurve I t ht n).curve.hom
    (algebraicEmbedding I t ht n) (algebraicEmbedding_structure I t ht n)
    (integralSmoothOpen (equation (algebraicParameter I t ht n))).ι rfl
    (recoveredSmoothFactor I t ht n) (recoveredSmoothFactor_structure I t ht n)
    (recoveredSmoothFactor_inclusion I t ht n)

/-- A finite coefficient enlargement retaining the actual smooth factor. -/
def algebraicSmoothStage : (CoefficientStage (algebraicBase I t ht n))ᵒᵖ :=
  (exists_algebraicSmoothStage I t ht n).choose

/-- The descended smooth factor, with target the original coefficient smooth model. -/
def algebraicSmoothFactor :
    (coefficientModelDiagram (algebraicBase I t ht n)
      (algebraicCarrier I t ht n).hom).obj (algebraicSmoothStage I t ht n) ⟶
        (integralSmoothOpen (equation (algebraicParameter I t ht n))).toScheme :=
  (exists_algebraicSmoothStage I t ht n).choose_spec.choose

/-- The descended factor recovers the actual original factor. -/
@[reassoc] theorem algebraicSmoothFactor_recovery :
    (coefficientModelCone (algebraicBase I t ht n)
      (algebraicCarrier I t ht n).hom).π.app (algebraicSmoothStage I t ht n) ≫
        algebraicSmoothFactor I t ht n = recoveredSmoothFactor I t ht n :=
  (exists_algebraicSmoothStage I t ht n).choose_spec.choose_spec.1

/-- The descended smooth factor remains over the fixed initial coefficient base. -/
@[reassoc] theorem algebraicSmoothFactor_structure :
    algebraicSmoothFactor I t ht n ≫
      integralSmoothStructure (equation (algebraicParameter I t ht n)) =
        (coefficientModelToInitial (algebraicBase I t ht n)
          (algebraicCarrier I t ht n).hom).app (algebraicSmoothStage I t ht n) ≫
            (algebraicCarrier I t ht n).hom :=
  (exists_algebraicSmoothStage I t ht n).choose_spec.choose_spec.2.1

/-- The exact original embedding is its whole-cubic composite at the same stage. -/
@[reassoc] theorem algebraicSmoothFactor_inclusion :
    algebraicSmoothFactor I t ht n ≫
      (integralSmoothOpen (equation (algebraicParameter I t ht n))).ι =
        (coefficientModelToInitial (algebraicBase I t ht n)
          (algebraicCarrier I t ht n).hom).app (algebraicSmoothStage I t ht n) ≫
            algebraicEmbedding I t ht n :=
  (exists_algebraicSmoothStage I t ht n).choose_spec.choose_spec.2.2

end FLT.Mazur.OneGonAdicCharacterTower
