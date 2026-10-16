/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapMobiusBoundary
public import FLT.Mazur.WeierstrassModificationXNodeOverlapInfinityIso
public import FLT.Mazur.WeierstrassModificationXInitialInfinityTransition

/-!
# Full fractional boundary squares on the original infinity localization

The actual original y-boundary, with all divided coefficients present, maps
to both fractional node charts and retains its projective infinity transition.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "E" => polynomialNodeOverlapInfinityIso W s b3 b4 b6 r hr I hI hrI h3
local notation "i" => polynomialNodeOverlapInclusion W s
local notation "j" => polynomialNodeOverlapOpposite W s b3 b4 b6 r hr I hI hrI h3
local notation "F" => polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3
local notation "G" => polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3

/-- The full original infinity boundary has its actual first fractional parameter. -/
def initialInfinityMobiusParameter : Spec (.of Y) ⟶ PolygonSmoothing.branchTorus R :=
  (E).inv ≫ initialMobiusOverlapParameter W s

/-- The same original infinity boundary retains its separate opposite fractional parameter. -/
def initialInfinityOppositeMobiusParameter : Spec (.of Y) ⟶ PolygonSmoothing.branchTorus R :=
  (E).inv ≫ initialMobiusOverlapOppositeParameter W s b3 b4 b6 r hr I hI hrI h3

/-- The entire original infinity localization has the first arithmetic polygon square. -/
@[reassoc] theorem initialInfinityMobiusParameter_boundary :
    (E).inv ≫ i ≫ initialMobiusChart W ha s τ hτ =
      initialInfinityMobiusParameter W s b3 b4 b6 r hr I hI hrI h3 ≫
        PolygonSmoothing.rightBranchOpen R τ := by
  rw [initialMobiusChart_overlap_first, initialInfinityMobiusParameter, Category.assoc]

/-- The entire original infinity localization has the actual reflected polygon square. -/
@[reassoc] theorem initialInfinityOppositeMobiusParameter_boundary :
    (E).inv ≫ j ≫ initialMobiusChart W ha s τ hτ =
      initialInfinityOppositeMobiusParameter W s b3 b4 b6 r hr I hI hrI h3 ≫
        PolygonSmoothing.rightBranchOpen R τ := by
  rw [initialMobiusChart_overlap_opposite, initialInfinityOppositeMobiusParameter,
    Category.assoc]

/-- Both full initial restrictions from infinity agree in the original initial affine scheme. -/
@[reassoc] theorem initialInfinityMobius_original_opposite :
    (E).inv ≫ j ≫ G = polynomialInitialInfinityInclusion W s b3 b4 b6 := by
  rw [polynomialNodeOverlapOpposite_global, polynomialNodeOverlapInfinityIso_inv_inclusion]

variable (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)

/-- The same first full restriction retains the original projective infinity transition. -/
@[reassoc] theorem initialInfinityMobius_original_transition :
    (E).inv ≫ i ≫ F ≫ toCurve W s b3 b4 b6 h₃ h₄ h₆ =
      Spec.map (CommRingCat.ofHom
        (initialInfinityTransition W s b3 b4 b6 h₃ h₄ h₆).toRingHom) ≫
          WeierstrassIntegralChart.integralCurveChart W 1 := by
  rw [polynomialNodeOverlapInfinityIso_inv_inclusion_assoc,
    initialInfinityTransition_toCurve]
  rfl

/-- The actual opposite full restriction retains that very same projective transition. -/
@[reassoc] theorem initialInfinityOppositeMobius_original_transition :
    (E).inv ≫ j ≫ G ≫ toCurve W s b3 b4 b6 h₃ h₄ h₆ =
      Spec.map (CommRingCat.ofHom
        (initialInfinityTransition W s b3 b4 b6 h₃ h₄ h₆).toRingHom) ≫
          WeierstrassIntegralChart.integralCurveChart W 1 := by
  rw [polynomialNodeOverlapOpposite_global_assoc]
  exact initialInfinityMobius_original_transition W s b3 b4 b6 r hr I hI hrI h3 h₃ h₄ h₆

end FLT.Mazur.WeierstrassModificationX
