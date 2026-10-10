/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleSplitOppositeConic
public import FLT.Mazur.PrincipalOpenTransportGeometry
public import FLT.Mazur.WeierstrassSuccessiveXMiddleComponents
public import FLT.Mazur.WeierstrassModificationXConicGeometry

/-!
# Full branch comparisons on the original middle tangent opens

The two branches of each actual principal-open chart are the original conic
parameter and horizontal line. The second conic parameter keeps its sign change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] (W : WeierstrassCurve K) (c : K) (hc : c = 0)
  (h2 : W.a₂ = 0) (ha : IsUnit W.a₁)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "C₀" => ConicCoordinate W.a₁ c
local notation "d" => coord W 0 0 0 0 c 1 + algebraMap K A W.a₁
local notation "J₁" => PrincipalOpenTransport.chart d (middleFirstNodeEquiv W c h2 ha)
local notation "J₂" => PrincipalOpenTransport.chart (-coord W 0 0 0 0 c 1)
  (middleSecondNodeEquiv W c h2 ha)

/-- The original first node inclusion is induced by its complete coordinate map. -/
theorem middleFirstNodeChart_eq_spec :
    J₁ = Spec.map (CommRingCat.ofHom (middleFirstToNodeBase W c h2).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (middleFirstToNode_base W c h2 ha)

/-- The original opposite inclusion retains the complete tangent involution. -/
theorem middleSecondNodeChart_eq_spec :
    J₂ = Spec.map (CommRingCat.ofHom
      ((middleFirstToNodeBase W c h2).comp (middleTangentSwitch W c h2)).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  change middleSecondNodeEquiv W c h2 ha (algebraMap A _ q) = _
  rw [middleSecondNodeEquiv_base]
  exact middleFirstToNode_base W c h2 ha _

/-- The explicit first parameter map is the inverse of the original conic chart. -/
theorem middleConicFirstParameter_map :
    conicToParameter W.a₁ c = (conicFirstParameterEquiv W.a₁ c ha).symm.toAlgHom.comp
      (Algebra.algHom K C₀ (ConicFirstOpen W.a₁ c)) := by
  apply AlgHom.ext
  intro q
  exact (conicFirstToParameter_base W.a₁ c ha q).symm

/-- The first node's conic branch is the complete original first parameter chart. -/
@[reassoc] theorem middleNodeFirstBranch_firstChart :
    middleNodeFirstBranch c hc ≫ J₁ =
      (conicZeroAffineIso c hc).hom ≫ (conicFirstParameterIso W.a₁ c ha).inv ≫
        conicFirstOpenImmersion W.a₁ c ≫ middleConicImmersion W c h2 := by
  rw [middleNodeFirstBranch_eq_spec, middleFirstNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  have h := middleSplitFirstRestriction_conic W c hc h2
  rw [middleConicFirstParameter_map W c ha] at h
  exact congrArg (fun f : A →ₐ[K] K[X] => Spec.map (CommRingCat.ofHom f.toRingHom)) h

/-- The opposite conic branch uses the negative of the original second parameter. -/
@[reassoc] theorem middleNodeFirstBranch_secondChart :
    middleNodeFirstBranch c hc ≫ J₂ =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        (conicZeroAffineIso c hc).hom ≫ (conicSecondParameterIso W.a₁ c ha).inv ≫
          conicSecondOpenImmersion W.a₁ c ≫ middleConicImmersion W c h2 := by
  rw [middleNodeFirstBranch_eq_spec, middleSecondNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ =
    Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[K] K[X] => Spec.map (CommRingCat.ofHom f.toRingHom))
    (middleSplitFirstRestriction_opposite_conic c hc W h2 ha)

/-- The first node's horizontal branch is the full original zero-slope line. -/
@[reassoc] theorem middleNodeSecondBranch_firstChart :
    middleNodeSecondBranch c hc ≫ J₁ =
      middleLineImmersion W c h2 0 (middle_first_root W) := by
  rw [middleNodeSecondBranch_eq_spec, middleFirstNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[K] K[X] => Spec.map (CommRingCat.ofHom f.toRingHom))
    (middleSplitSecondRestriction_line W c hc h2)

/-- The opposite node's horizontal branch is the full original opposite-slope line. -/
@[reassoc] theorem middleNodeSecondBranch_secondChart :
    middleNodeSecondBranch c hc ≫ J₂ =
      middleLineImmersion W c h2 (-W.a₁) (middle_second_root W) := by
  rw [middleNodeSecondBranch_eq_spec, middleSecondNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f : A →ₐ[K] K[X] => Spec.map (CommRingCat.ofHom f.toRingHom))
    (middleSplitSecondRestriction_opposite_line W c hc h2)

end FLT.Mazur.WeierstrassSuccessiveX
