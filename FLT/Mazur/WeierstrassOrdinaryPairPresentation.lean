/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryDomainLift
public import FLT.Mazur.WeierstrassLeftSmoothFormulaComparison
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# Ordinary presentations constructed from the actual affine inputs

An invertible ordinary denominator constructs the addition chart map. Its
input contractions and its agreement with the genuine smooth action follow
from the universal properties, without assuming an output comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (a c : Coordinate W 2 →ₐ[R] S) (b : Bool)
  (h : IsUnit (chartProductEvaluation W 2 2 a c
    (if b then tangentDenominator W else secantDenominator W)))

/-- The actual ordinary chart presentation of a pair with invertible denominator. -/
def ordinaryPairPresentation : additionChartRing W (ordinaryIndex b) →ₐ[R] S :=
  ordinaryDomainLift W b (chartProductEvaluation W 2 2 a c) h

/-- The constructed presentation recovers the original left input. -/
theorem ordinaryPairPresentation_left :
    (ordinaryPairPresentation W a c b h).comp (ordinaryInputLeft W b) = a := by
  change (ordinaryDomainLift W b _ h).comp
    ((additionChartAlgRestriction W (ordinaryIndex b)).comp (productLeft W)) = a
  rw [← AlgHom.comp_assoc, ordinaryDomainLift_restriction]
  exact chartProductEvaluation_left W 2 2 a c

/-- The constructed presentation recovers the original right input. -/
theorem ordinaryPairPresentation_right :
    (ordinaryPairPresentation W a c b h).comp (ordinaryInputRight W b) = c := by
  change (ordinaryDomainLift W b _ h).comp
    ((additionChartAlgRestriction W (ordinaryIndex b)).comp (productRight W)) = c
  rw [← AlgHom.comp_assoc, ordinaryDomainLift_restriction]
  exact chartProductEvaluation_right W 2 2 a c

variable (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    p ≫ (integralSmoothOpen W).ι)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)

include ha in
/-- The constructed ordinary domain has the actual smooth by whole input pair. -/
theorem ordinaryPairPresentation_inputs :
    Spec.map (CommRingCat.ofHom (ordinaryPairPresentation W a c b h).toRingHom) ≫
        ordinaryGlobalDomain W b =
      pullback.lift p (Spec.map (CommRingCat.ofHom c.toRingHom) ≫
        integralCurveChart W 2) hp ≫ leftSmoothFactorsInclusion W := by
  apply pullback.hom_ext
  · rw [Category.assoc, ordinaryGlobalDomain_fst, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((ordinaryPairPresentation W a c b h).comp (ordinaryInputLeft W b)).toRingHom) ≫
      integralCurveChart W 2 = _
    rw [ordinaryPairPresentation_left, ha, Category.assoc,
      leftSmoothFactorsInclusion_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, ordinaryGlobalDomain_snd, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((ordinaryPairPresentation W a c b h).comp (ordinaryInputRight W b)).toRingHom) ≫
      integralCurveChart W 2 = _
    rw [ordinaryPairPresentation_right, Category.assoc,
      leftSmoothFactorsInclusion_snd, pullback.lift_snd]

include ha in
/-- Its affine output is the genuine smooth action, including on singular fibers. -/
theorem ordinaryPairPresentation_addition :
    Spec.map (CommRingCat.ofHom
      ((ordinaryPairPresentation W a c b h).comp (ordinaryChartAddition W b)).toRingHom) ≫
        integralCurveChart W 2 =
      leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) hp := by
  have he := leftSmoothFactorAddition_ordinary W
    (pullback.lift p (Spec.map (CommRingCat.ofHom c.toRingHom) ≫
      integralCurveChart W 2) hp) b
    (Spec.map (CommRingCat.ofHom (ordinaryPairPresentation W a c b h).toRingHom))
    (ordinaryPairPresentation_inputs W a c b h p ha hp)
  rw [← Category.assoc, ← Spec.map_comp] at he
  exact he.symm

end FLT.Mazur.WeierstrassIntegralChart
