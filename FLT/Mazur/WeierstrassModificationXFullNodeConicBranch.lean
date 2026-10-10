/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeConicParameter
public import FLT.Mazur.WeierstrassModificationXFullNodeFunctions
public import FLT.Mazur.WeierstrassModificationXConicGeometry
public import FLT.Mazur.WeierstrassModificationXConicSecondCoordinates
public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# The node's conic branches are the original rational component maps

Both signed branch maps agree with the original conic parameterizations as
scheme morphisms. This preserves the opposite tangent's slope translation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] (a c : K) (ha : IsUnit a)
local notation "P" => ConicParameterOpen c
local notation "F" => FiberCoordinate a c
local notation "C₀" => ConicCoordinate a c

/-- The entire first original fiber map is the original rational conic parameterization. -/
theorem fullNodeConicRestriction_firstFiber :
    (fullNodeConicRestriction a c ha).comp (fiberFullFirstNodeMap a c ha) =
      ((conicFirstParameterEquiv a c ha).symm.toAlgHom.comp
        (Algebra.algHom K C₀ (ConicFirstOpen a c))).comp (fiberConicMap a c) := by
  apply fiber_hom_ext
  · simp only [AlgHom.comp_apply, fiberFullFirstNodeMap_t, fullNodeConicRestriction_inverseT,
      fiberConicMap_t]
    rw [conicFirstParameterEquiv_symm_toAlgHom]
    simpa only [conicToParameter_t, Algebra.algHom, IsScalarTower.toAlgHom_apply] using
      (conicFirstToParameter_base a c ha (conicT a c)).symm
  · simp only [AlgHom.comp_apply, fiberFullFirstNodeMap_v, fullNodeConicRestriction_inverseV,
      fiberConicMap_v]
    rw [conicFirstParameterEquiv_symm_toAlgHom]
    simpa only [conicToParameter_v, Algebra.algHom, IsScalarTower.toAlgHom_apply] using
      (conicFirstToParameter_base a c ha (conicV a c)).symm

/-- The entire second original fiber map is the opposite rational conic parameterization. -/
theorem fullNodeConicRestriction_secondFiber :
    (fullNodeConicRestriction (-a) c ha.neg).comp (fiberFullSecondNodeMap a c ha) =
      ((conicSecondParameterEquiv a c ha).symm.toAlgHom.comp
        (Algebra.algHom K C₀ (ConicSecondOpen a c))).comp (fiberConicMap a c) := by
  apply fiber_hom_ext
  · simp only [AlgHom.comp_apply, fiberFullSecondNodeMap_t, fullNodeConicRestriction_inverseT,
      fiberConicMap_t]
    exact (conicSecondParameterEquiv_symm_t a c ha).symm
  · simp only [AlgHom.comp_apply, fiberFullSecondNodeMap_v, map_sub, AlgHom.commutes,
      fullNodeConicRestriction_inverseV, fiberConicMap_v]
    exact (conicSecondParameterEquiv_symm_v a c ha).symm

/-- The original parameter scheme is precisely the first localized branch source. -/
def fullNodeConicParameterIso : Spec (.of P) ≅ Spec (.of
    (Localization.Away (PolygonNodeEqualizer.first (fullNodeNormalizedDenominator a c)))) :=
  Scheme.Spec.mapIso (fullNodeConicParameterEquiv a c ha).toRingEquiv.toCommRingCatIso.op

/-- The first node's conic branch is exactly the original first conic affine map. -/
@[reassoc] theorem fullNodeFirstBranch_firstChart :
    (fullNodeConicParameterIso a c ha).hom ≫ fullNodeFirstBranch a c ha ≫
      fullFirstNodeChart a c ha =
    (conicFirstParameterIso a c ha).inv ≫ conicFirstOpenImmersion a c ≫
      fiberConicImmersion a c := by
  rw [fullNodeFirstBranch_eq_spec, fullFirstNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : F →ₐ[K] P => Spec.map (CommRingCat.ofHom f.toRingHom))
    (fullNodeConicRestriction_firstFiber a c ha)

/-- The opposite node's conic branch is exactly the original second conic affine map. -/
@[reassoc] theorem fullNodeFirstBranch_secondChart :
    (fullNodeConicParameterIso (-a) c ha.neg).hom ≫ fullNodeFirstBranch (-a) c ha.neg ≫
      fullSecondNodeChart a c ha =
    (conicSecondParameterIso a c ha).inv ≫ conicSecondOpenImmersion a c ≫
      fiberConicImmersion a c := by
  rw [fullNodeFirstBranch_eq_spec, fullSecondNodeChart_eq_spec]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f : F →ₐ[K] P => Spec.map (CommRingCat.ofHom f.toRingHom))
    (fullNodeConicRestriction_secondFiber a c ha)

end FLT.Mazur.WeierstrassModificationX
