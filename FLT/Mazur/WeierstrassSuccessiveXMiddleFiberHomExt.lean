/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterBranchCharts
public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterDescent
public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.BinaryOpenDescent

/-!
# The full retained middle equation is detected by its original components

The two localized node pushouts and their open cover detect maps to arbitrary
schemes, retaining the whole conic and both horizontal lines at every constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W 0 0 0 0 c 1 + algebraMap K A W.a₁) (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)

/-- Both original tangent neighborhoods cover the entire middle equation. -/
theorem middleParameterCharts_cover (x : Spec (.of A)) :
    x ∈ Set.range J₁ ∨ x ∈ Set.range J₂ := by
  rw [PrincipalOpenTransport.chart_range, PrincipalOpenTransport.chart_range]
  exact middle_tangent_opens_cover W c ha x

include ha in
/-- The conic and both complete horizontal lines determine any map from the middle chart. -/
theorem middleFiber_components_hom_ext {Y : Scheme.{u}} (f g : Spec (.of A) ⟶ Y)
    (hC : middleConicImmersion W c h2 ≫ f = middleConicImmersion W c h2 ≫ g)
    (h₁ : middleLineImmersion W c h2 0 (middle_first_root W) ≫ f =
      middleLineImmersion W c h2 0 (middle_first_root W) ≫ g)
    (h₂ : middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) ≫ f =
      middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) ≫ g) : f = g := by
  apply BinaryOpenDescent.hom_ext J₁ J₂ (middleParameterCharts_cover W c h2 ha)
  · apply middleParameter_hom_ext c
    · rw [middleParameterConicBranch_firstChart_assoc,
        middleParameterConicBranch_firstChart_assoc, hC]
    · rw [middleParameterLineBranch_firstChart_assoc,
        middleParameterLineBranch_firstChart_assoc, h₁]
  · apply middleParameter_hom_ext c
    · rw [middleParameterConicBranch_secondChart_assoc,
        middleParameterConicBranch_secondChart_assoc, hC]
    · rw [middleParameterLineBranch_secondChart_assoc,
        middleParameterLineBranch_secondChart_assoc, h₂]

end FLT.Mazur.WeierstrassSuccessiveX
