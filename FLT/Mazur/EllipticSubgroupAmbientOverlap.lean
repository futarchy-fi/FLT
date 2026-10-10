/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupOverlapGraph
public import FLT.Mazur.WeierstrassIntegralCurveGluing

/-!
# The subgroup closure overlap maps into the ambient cubic overlap

The quotient and localization comparison makes the two closure chart
inclusions commute with the original homogeneous transition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The quotient inclusion of each actual subgroup closure chart into its cubic chart. -/
def closureAmbientChart : closureChart A W H j ⟶ chartScheme W j :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- Each ambient chart inclusion is a closed immersion, by its actual kernel quotient. -/
instance closureAmbientChart_isClosedImmersion : IsClosedImmersion (closureAmbientChart A W H j) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Ambient overlap coordinates restricted to the actual closure overlap. -/
def ambientOverlapMap : Overlap W j k →ₐ[A] LocalizedClosure A W H j k :=
  (closureLocalizationEquiv A W H j k).symm.toAlgHom.comp (Ideal.Quotient.mkₐ A _)

/-- On the original chart, the overlap map is the quotient followed by localization. -/
theorem ambientOverlapMap_algebraMap (x : Coordinate W j) :
    ambientOverlapMap A W H j k (algebraMap (Coordinate W j) (Overlap W j k) x) =
      algebraMap (Closure A W H j) (LocalizedClosure A W H j k) (Ideal.Quotient.mk _ x) := by
  apply (closureLocalizationEquiv A W H j k).injective
  simp only [ambientOverlapMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  exact ((IsLocalization.algEquiv (Submonoid.powers (closureCoord A W H j k))
    (LocalizedClosure A W H j k) (OverlapClosure A W H j k)).commutes (Ideal.Quotient.mk _ x)).symm

/-- Restricting the opposite chart agrees with the actual descended transition. -/
theorem ambientOverlapMap_transition (x : Overlap W k j) :
    ambientOverlapMap A W H j k (transition W j k x) =
      localizedClosureEquiv A W H j k (ambientOverlapMap A W H k j x) := by
  apply (closureLocalizationEquiv A W H j k).injective
  simp only [ambientOverlapMap, localizedClosureEquiv, AlgHom.comp_apply,
    AlgEquiv.trans_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, Ideal.Quotient.mkₐ_eq_mk, closureOverlapEquiv_mk]

/-- The actual closure overlap has a morphism into the ambient overlap. -/
def closureAmbientOverlap : closureIntersection A W H j k ⟶ overlapScheme W j k :=
  Spec.map (CommRingCat.ofHom (ambientOverlapMap A W H j k).toRingHom)

/-- The ambient overlap morphism retains the first chart inclusion. -/
@[reassoc] theorem closureAmbientOverlap_left :
    closureAmbientOverlap A W H j k ≫ overlapInclusion W j k =
      closureToLeft A W H j k ≫ closureAmbientChart A W H j := by
  rw [closureAmbientOverlap, overlapInclusion, PrincipalAffineRefinement.inclusion,
    closureToLeft, closureAmbientChart,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (ambientOverlapMap_algebraMap A W H j k)

/-- The ambient overlap morphism retains the opposite chart after its transition. -/
@[reassoc] theorem closureAmbientOverlap_right :
    closureAmbientOverlap A W H j k ≫ chartTransition W j k ≫ overlapInclusion W k j =
      closureToRight A W H j k ≫ closureAmbientChart A W H k := by
  simp only [closureAmbientOverlap, chartTransition, overlapInclusion,
    PrincipalAffineRefinement.inclusion, closureToRight,
    closureIntersectionIso, Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op, closureToLeft, closureAmbientChart,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (ambientOverlapMap_transition A W H j k _).trans
    (congrArg (localizedClosureEquiv A W H j k) (ambientOverlapMap_algebraMap A W H k j x))

end FLT.Mazur.EllipticSubgroupChart
