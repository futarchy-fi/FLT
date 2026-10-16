/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialInfinityTransition
public import FLT.Mazur.PrincipalOpenTensorGeometry
public import FLT.Mazur.WeierstrassChartBaseChange

/-!
# The complete original infinity transition after coefficient extension

The original localization map extends to the actual tensor boundary. Its
projection preserves all original infinity functions, including X/Y.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (S : Type u) [CommRing S] [Algebra R S]
local notation "y" => WeierstrassModificationX.y W s b3 b4 b6
local notation "Y" => Localization.Away ((1 : S) ⊗ₜ[R] y)
local notation "f" => initialInfinityTransition W s b3 b4 b6 h3 h4 h6
open WeierstrassIntegralChart

/-- Extend the original initial infinity transition to the full tensor principal open. -/
def initialInfinityTensorTransition : ChartScalarExtension S W 1 →ₐ[S] Y :=
  AlgHom.liftEquiv R S _ _ ((PrincipalOpenTensor.coefficient (R := R) S y).comp f)

local notation "F" => initialInfinityTensorTransition W s b3 b4 b6 h3 h4 h6 S

/-- Every original infinity function retains its original transition value. -/
theorem initialInfinityTensorTransition_tmul (a : S)
    (w : WeierstrassIntegralChart.Coordinate W 1) :
    F (a ⊗ₜ[R] w) = a • PrincipalOpenTensor.coefficient (R := R) S y (f w) := rfl

/-- The actual infinity X/Y survives tensor extension as the original localized quotient. -/
theorem initialInfinityTensorTransition_x :
    F ((1 : S) ⊗ₜ[R] coord W 1 0) =
      PrincipalOpenTensor.coefficient (R := R) S y
        (algebraMap (WeierstrassModificationX.Coordinate W s b3 b4 b6) (Localization.Away y)
          (x W s b3 b4 b6) * IsLocalization.Away.invSelf y) := by
  rw [initialInfinityTensorTransition_tmul, one_smul,
    initialInfinityTransition_x]

/-- The full tensor transition projects to the same original integral transition. -/
@[reassoc] theorem initialInfinityTensorTransition_projection :
    Spec.map (CommRingCat.ofHom (F).toRingHom) ≫
      TensorOpenChart.projection (R := R) (S := S) =
      PrincipalOpenTensor.projection S y ≫ Spec.map (CommRingCat.ofHom (f).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun w => one_smul S (PrincipalOpenTensor.coefficient (R := R) S y (f w)))

/-- The tensor transition agrees with the original initial contraction in the projective curve. -/
@[reassoc] theorem initialInfinityTensorTransition_toCurve :
    Spec.map (CommRingCat.ofHom (F).toRingHom) ≫
      TensorOpenChart.projection (R := R) (S := S) ≫
      integralCurveChart W 1 =
        PrincipalOpenTensor.inclusion S y ≫ TensorOpenChart.projection (R := R) (S := S) ≫
          toCurve W s b3 b4 b6 h3 h4 h6 := by
  rw [initialInfinityTensorTransition_projection_assoc, initialInfinityTransition_toCurve]
  rw [PrincipalOpenTensor.inclusion_projection_assoc]

end FLT.Mazur.WeierstrassModificationX
