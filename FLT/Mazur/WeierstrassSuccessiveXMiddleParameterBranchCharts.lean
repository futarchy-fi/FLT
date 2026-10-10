/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterPushout
public import FLT.Mazur.WeierstrassSuccessiveXMiddleLocalizedOppositeConic
public import FLT.Mazur.WeierstrassSuccessiveXMiddleSplitBranchCharts

/-!
# Full original branch comparisons for arbitrary middle constant

Both tangent neighborhoods retain their complete conic parameter opens and
horizontal lines. The opposite conic comparison keeps its parameter negation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c : K)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "J₁" => PrincipalOpenTransport.chart
  (coord W 0 0 0 0 c 1 + algebraMap K A W.a₁) (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)

/-- The full original first conic parameter branch, including nonzero constant. -/
@[reassoc] theorem middleParameterConicBranch_firstChart :
    middleParameterConicBranch c ≫ J₁ =
      (conicFirstParameterIso W.a₁ c ha).inv ≫
        conicFirstOpenImmersion W.a₁ c ≫ middleConicImmersion W c h2 := by
  rw [middleParameterConicBranch, middleFirstNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  have h := middleLocalizedConicRestriction_conic c W h2
  rw [middleConicFirstParameter_map W c ha] at h
  exact congrArg (fun f : A →ₐ[K] ConicParameterOpen c =>
    Spec.map (CommRingCat.ofHom f.toRingHom)) h

/-- The opposite full conic branch retains its original signed second parameter. -/
@[reassoc] theorem middleParameterConicBranch_secondChart :
    middleParameterConicBranch c ≫ J₂ =
      Spec.map (CommRingCat.ofHom (conicParameterNeg c).toRingHom) ≫
        (conicSecondParameterIso W.a₁ c ha).inv ≫
          conicSecondOpenImmersion W.a₁ c ≫ middleConicImmersion W c h2 := by
  rw [middleParameterConicBranch, middleSecondNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[K] ConicParameterOpen c =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
      (middleLocalizedConicRestriction_opposite_conic W c h2 ha)

/-- The entire first horizontal branch is unchanged on the original first node chart. -/
@[reassoc] theorem middleParameterLineBranch_firstChart :
    middleParameterLineBranch c ≫ J₁ =
      middleLineImmersion W c h2 0 (middle_first_root W) := by
  rw [middleParameterLineBranch, middleFirstNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[K] K[X] => Spec.map (CommRingCat.ofHom f.toRingHom))
    (middleLocalizedLineRestriction_line c W h2)

/-- The entire opposite horizontal branch is unchanged on the original second node chart. -/
@[reassoc] theorem middleParameterLineBranch_secondChart :
    middleParameterLineBranch c ≫ J₂ =
      middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) := by
  rw [middleParameterLineBranch, middleSecondNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[K] K[X] => Spec.map (CommRingCat.ofHom f.toRingHom))
    (middleLocalizedLineRestriction_opposite_line c W h2)

end FLT.Mazur.WeierstrassSuccessiveX
