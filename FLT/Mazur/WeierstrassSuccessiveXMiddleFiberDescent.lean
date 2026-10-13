/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleDescentCompatibility
public import FLT.Mazur.WeierstrassSuccessiveXMiddleFiberHomExt
public import FLT.Mazur.WeierstrassModificationXConicParameterHomExt

/-!
# Descent from the full conic and two lines of the retained middle equation

Construct an actual morphism to any target from the original three component
maps agreeing at their two origins. The divided constant may be nonzero.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W 0 0 0 0 c 1 + algebraMap K A W.a₁) (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)

local notation "p₁" => (conicFirstParameterIso W.a₁ c ha).inv ≫
  conicFirstOpenImmersion W.a₁ c
local notation "p₂" => Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
  (conicSecondParameterIso W.a₁ c ha).inv ≫ conicSecondOpenImmersion W.a₁ c

local notation "o" => Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom)
variable {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate W.a₁ c)) ⟶ Y)
  (g₁ g₂ : ProjectiveLine.chart K ⟶ Y)

/-- Compatible complete component maps descend across both original node charts. -/
def middleFiberDesc
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) : Spec (.of A) ⟶ Y :=
  BinaryOpenDescent.desc (pullback.fst J₁ J₂) (pullback.snd J₁ J₂) J₁ J₂
    (IsPullback.of_hasPullback J₁ J₂) (middleParameterCharts_cover W c h2 ha)
    (middleParameterDesc c (p₁ ≫ f) g₁ w₁) (middleParameterDesc c (p₂ ≫ f) g₂ w₂)
    (middleNodeDescents_compatible W c h2 ha f _ _
      (middleParameterConicBranch_desc c _ _ _) (middleParameterConicBranch_desc c _ _ _)
      _ _ pullback.condition)

/-- The descended map retains the complete first local node descent. -/
@[reassoc] theorem middleFiberDesc_firstChart
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) :
    J₁ ≫ middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂ =
      middleParameterDesc c (p₁ ≫ f) g₁ w₁ :=
  BinaryOpenDescent.inl_desc ..

/-- The opposite node descent keeps its original negated parameter. -/
@[reassoc] theorem middleFiberDesc_secondChart
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) :
    J₂ ≫ middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂ =
      middleParameterDesc c (p₂ ≫ f) g₂ w₂ :=
  BinaryOpenDescent.inr_desc ..

/-- Descent recovers the entire first horizontal line. -/
@[reassoc] theorem middleFiberDesc_firstLine
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) :
    middleLineImmersion W c h2 0 (middle_first_root W) ≫
      middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂ = g₁ := by
  rw [← middleParameterLineBranch_firstChart W c h2 ha, Category.assoc,
    middleFiberDesc_firstChart, middleParameterLineBranch_desc]

/-- Descent recovers the entire opposite horizontal line. -/
@[reassoc] theorem middleFiberDesc_secondLine
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) :
    middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) ≫
      middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂ = g₂ := by
  rw [← middleParameterLineBranch_secondChart W c h2 ha, Category.assoc,
    middleFiberDesc_secondChart, middleParameterLineBranch_desc]

/-- Descent recovers all original conic functions, on both entire parameter opens. -/
@[reassoc] theorem middleFiberDesc_conic
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) :
    middleConicImmersion W c h2 ≫ middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂ = f := by
  apply conicParameter_hom_ext W.a₁ c ha
  · simp only [Category.assoc]
    rw [← middleParameterConicBranch_firstChart_assoc, middleFiberDesc_firstChart,
      middleParameterConicBranch_desc]
    simp only [Category.assoc]
  · let ν := Scheme.Spec.mapIso (conicParameterNeg c).toCommRingCatIso.op
    apply (cancel_epi ν.hom).mp
    simp only [Category.assoc]
    change p₂ ≫ middleConicImmersion W c h2 ≫
      middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂ = _
    simp only [Category.assoc]
    rw [← middleParameterConicBranch_secondChart_assoc, middleFiberDesc_secondChart,
      middleParameterConicBranch_desc]
    rfl

/-- The original full conic and both lines give the unique morphism with those restrictions. -/
theorem middleFiber_exists_unique_desc
    (w₁ : o ≫ p₁ ≫ f = ProjectiveLine.chartZero K ≫ g₁)
    (w₂ : o ≫ p₂ ≫ f = ProjectiveLine.chartZero K ≫ g₂) :
    ∃! d : Spec (.of A) ⟶ Y, middleConicImmersion W c h2 ≫ d = f ∧
      middleLineImmersion W c h2 0 (middle_first_root W) ≫ d = g₁ ∧
      middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) ≫ d = g₂ := by
  refine ⟨middleFiberDesc W c h2 ha f g₁ g₂ w₁ w₂,
    ⟨middleFiberDesc_conic W c h2 ha f g₁ g₂ w₁ w₂,
      middleFiberDesc_firstLine W c h2 ha f g₁ g₂ w₁ w₂,
      middleFiberDesc_secondLine W c h2 ha f g₁ g₂ w₁ w₂⟩, ?_⟩
  intro d hd
  apply middleFiber_components_hom_ext W c h2 ha
  · rw [hd.1, middleFiberDesc_conic]
  · rw [hd.2.1, middleFiberDesc_firstLine]
  · rw [hd.2.2, middleFiberDesc_secondLine]

end FLT.Mazur.WeierstrassSuccessiveX
