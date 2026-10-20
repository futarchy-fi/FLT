/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalChartSpecialization
public import FLT.Mazur.WeierstrassLeftSmoothFormulaComparison
public import FLT.Mazur.WeierstrassChartEvaluationComparison

/-!
# The original smooth action on any actual reciprocal presentation

Both complete input maps identify a reciprocal chart with the genuine original
smooth action. The equality is valid over arbitrary coefficient algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (a c : Coordinate W 2 →ₐ[R] S) (b : Bool)
  (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)
  (hl : f.comp (reciprocalInputLeft W b) = a)
  (hr : f.comp (reciprocalInputRight W b) = c)
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ integralCurveChart W 2 =
    p ≫ (integralSmoothOpen W).ι)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) ≫
      integralCurveStructure W)

include hl hr ha in
/-- A reciprocal presentation retains the actual smooth by whole input pair. -/
theorem reciprocalPresentation_inputs :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ reciprocalGlobalDomain W b =
      pullback.lift p (Spec.map (CommRingCat.ofHom c.toRingHom) ≫
        integralCurveChart W 2) hp ≫ leftSmoothFactorsInclusion W := by
  apply pullback.hom_ext
  · rw [Category.assoc, reciprocalGlobalDomain_fst, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (f.comp (reciprocalInputLeft W b)).toRingHom) ≫ integralCurveChart W 2 = _
    rw [hl, ha, Category.assoc,
      leftSmoothFactorsInclusion_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, reciprocalGlobalDomain_snd, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (f.comp (reciprocalInputRight W b)).toRingHom) ≫ integralCurveChart W 2 = _
    rw [hr, Category.assoc, leftSmoothFactorsInclusion_snd, pullback.lift_snd]

include hl hr ha in
/-- The normalized reciprocal output is exactly the genuine original smooth action. -/
theorem reciprocalPresentation_addition :
    Spec.map (CommRingCat.ofHom (f.comp (reciprocalChartAddition W b)).toRingHom) ≫
        integralCurveChart W 1 =
      leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom c.toRingHom) ≫ integralCurveChart W 2) hp := by
  have he := leftSmoothFactorAddition_reciprocal W
    (pullback.lift p (Spec.map (CommRingCat.ofHom c.toRingHom) ≫
      integralCurveChart W 2) hp) b (Spec.map (CommRingCat.ofHom f.toRingHom))
    (reciprocalPresentation_inputs W a c b f hl hr p ha hp)
  rw [← Category.assoc, ← Spec.map_comp] at he
  exact he.symm

end FLT.Mazur.WeierstrassIntegralChart
