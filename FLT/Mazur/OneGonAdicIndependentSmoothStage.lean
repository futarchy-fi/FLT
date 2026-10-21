/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentSmoothRecovery

/-!
# Finite coefficient descent of the actual canonical smooth factor

The fixed finite character source and the genuine one-gon model admit a
finite coefficient enlargement on which the canonical smooth factor descends.
Both its full cubic composite and its complete-base recovery are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicIndependentModel

open OneGonSmoothing WeierstrassIntegralChart Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)

/-- The original smooth factor and its original whole-cubic equation descend together. -/
theorem exists_smoothStage (hs : s.Finite) :
    ∃ (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
      (b : (coefficientModelDiagram (base I t ht n s)
        (carrier I t ht n s).hom).obj i ⟶
          (integralSmoothOpen (equation (parameter I t ht n s))).toScheme),
      (coefficientModelCone (base I t ht n s)
        (carrier I t ht n s).hom).π.app i ≫ b = recoveredSmoothFactor I t ht n s ∧
      b ≫ integralSmoothStructure (equation (parameter I t ht n s)) =
        (coefficientModelToInitial (base I t ht n s)
          (carrier I t ht n s).hom).app i ≫ (carrier I t ht n s).hom ∧
      b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
        (coefficientModelToInitial (base I t ht n s)
          (carrier I t ht n s).hom).app i ≫ embedding I t ht n s := by
  let _ := base_finiteType I t ht n s hs
  let _ := (carrier_degree I t ht n s).1
  exact exists_coefficient_factorization (base I t ht n s)
    (carrier I t ht n s).hom
    (integralSmoothStructure (equation (parameter I t ht n s)))
    (integralCurveStructure (equation (parameter I t ht n s)))
    (embedding I t ht n s) (embedding_structure I t ht n s)
    (integralSmoothOpen (equation (parameter I t ht n s))).ι rfl
    (recoveredSmoothFactor I t ht n s) (recoveredSmoothFactor_structure I t ht n s)
    (recoveredSmoothFactor_inclusion I t ht n s)

end FLT.Mazur.OneGonAdicIndependentModel
