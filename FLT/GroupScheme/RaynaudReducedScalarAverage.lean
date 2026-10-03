/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRankOneProjector

/-!
# The character average on all coordinates

Subtracting the zero scalar removes the counit component. This gives the
extended character projector as a linear combination of actual scalar maps.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open CharacterProjector WithConv

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K)
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))

include h0

omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- The zero scalar is the convolution unit on linear coordinate maps. -/
theorem FF.scalar_zero_conv : toConv (lift 0).toLinearMap =
    (1 : WithConv (X.CoordinateRing →ₗ[R] X.CoordinateRing)) := by
  rw [h0]
  rfl

/-- The extended character projector is the reduced scalar average. -/
theorem FF.coordinateCharacterProjector_average (χ : Fˣ →* Rˣ) :
    X.coordinateCharacterProjector lift h1 hmul χ =
      ⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ,
        (↑(χ u)⁻¹ : R) • ((lift u).toLinearMap - (lift 0).toLinearMap) := by
  ext a
  change (projector (X.augmentationRepresentation lift h1 hmul) χ
    (X.augmentationProjection a) : X.CoordinateRing) = _
  rw [projector_apply]
  simp only [Submodule.coe_smul, Submodule.coe_sum, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.sub_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  change lift u (a - algebraMap R X.CoordinateRing (Coalgebra.counit a)) = _
  rw [map_sub, AlgHomClass.commutes, h0]
  rfl

/-- The average can be used in the convolution algebra of linear maps. -/
theorem FF.coordinateCharacterProjector_conv_average (χ : Fˣ →* Rˣ) :
    toConv (X.coordinateCharacterProjector lift h1 hmul χ) =
      ⅟(Fintype.card Fˣ : R) • ∑ u : Fˣ,
        (↑(χ u)⁻¹ : R) • (toConv (lift u).toLinearMap - 1) := by
  rw [X.coordinateCharacterProjector_average lift h0 h1 hmul χ]
  rw [← X.scalar_zero_conv lift h0]
  simp only [toConv_smul, toConv_sum, toConv_sub]

end ThreeAdicPlan
