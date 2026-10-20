/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicCharacterAffineEffectivity
public import FLT.Mazur.WeierstrassChartCoefficientSurjectivity
public import FLT.Mazur.AffineClosedImmersionCoordinates

/-!
# The original initial embedding gives full initial coordinate surjectivity

Both the finite chart identification and its actual coefficient projection
preserve closed immersion. The initial coordinate map is therefore surjective
on the entire character algebra, including nonreduced coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommGroup G] (I : Ideal R) (t : R)
  (ht : t ∈ I) (g : stageSource I G 0 ⟶ stageGroup I t 0)

/-- Every full coefficient chart projection is a closed immersion. -/
instance chartProjection_isClosedImmersion (m : ℕ) :
    IsClosedImmersion (chartProjection I t m) :=
  IsClosedImmersion.spec_of_surjective _
    (chartCoefficientRingMapTo_surjective (Ideal.Quotient.mk (I ^ (m + 1)))
      (equation t) 1 Ideal.Quotient.mk_surjective (equation (parameter I t m))
      (equation_map t (Ideal.Quotient.mk _)))

/-- The initial map to the original whole-base chart retains its closed embedding. -/
theorem towerAffine_zero_isClosedImmersion [IsClosedImmersion g.hom.hom.hom.left] :
    IsClosedImmersion (towerAffine I t ht g 0) := by
  rw [towerAffine_zero]
  infer_instance

/-- The original initial embedding surjects onto the entire initial character algebra. -/
theorem towerCoordinates_zero_surjective [IsClosedImmersion g.hom.hom.hom.left] :
    Function.Surjective (towerCoordinates I t ht g 0) := by
  let _ := towerAffine_zero_isClosedImmersion I t ht g
  exact AffineClosedImmersionCoordinates.preimage_surjective (towerAffine I t ht g 0)

end FLT.Mazur.OneGonAdicCharacterTower
