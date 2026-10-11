/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationCenterSheaf
public import FLT.Mazur.WeierstrassAdditionCenterContainment
public import FLT.Mazur.WeierstrassAffineAdditionGluing
public import FLT.Mazur.AffineIdealContainment

/-!
# Full center sheaf containment on the original addition charts

The coefficient-ring calculations give actual pullback ideal containments on
all four affine addition domains and on each polynomial projective domain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)

/-- Ring-level center containment is exactly containment of the original global ideal pullbacks. -/
theorem modificationCenterSheaf_spec_le {S : Type u} [CommRing S] [Algebra R S]
    (j k : Fin 3) (f : Coordinate W j →ₐ[R] S) (g : Coordinate W k →ₐ[R] S)
    (h : (modificationChartCenter W s j).map f.toRingHom ≤
      (modificationChartCenter W s k).map g.toRingHom) :
    (modificationCenterSheaf W s).comap
        (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) ≤
      (modificationCenterSheaf W s).comap
        (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ integralCurveChart W k) := by
  simp only [comap_comp, modificationCenterSheaf_chart, modificationChartCenterSheaf,
    BaseAdicThickening.baseIdeal_comap_specMap]
  exact (BaseAdicThickening.baseIdeal_le_iff _ _ _).mpr h

include h3 h4 in
/-- All four genuine affine formulas preserve the full global center ideal. -/
theorem additionCurveChart_center_le (i : AdditionChartIndex) :
    (modificationCenterSheaf W s).comap (additionCurveChart W i) ≤
      (modificationCenterSheaf W s).comap
        (additionChartInclusion W i ≫ Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ≫
          integralCurveChart W 2) := by
  have hr (i : AdditionChartIndex) :
      (additionChartAlgRestriction W i : AffineProduct W →+* additionChartRing W i) =
        additionChartRestriction W i := additionChartAlgRestriction_toRingHom W i
  have ordinary (b : Bool) :
      (modificationCenterSheaf W s).comap (additionCurveChart W (ordinaryIndex b)) ≤
        (modificationCenterSheaf W s).comap
          (additionChartInclusion W (ordinaryIndex b) ≫
            Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ≫
              integralCurveChart W 2) := by
    have h := modificationCenterSheaf_spec_le W s 2 2
      (ordinaryChartAddition W b) (ordinaryInputRight W b)
      (ordinarySpecialization_center_le W s b (AlgHom.id R _) b3 b4 h3 h4)
    cases b <;>
      dsimp only [ordinaryIndex, reciprocalIndex, additionChartRing] at h ⊢ <;>
      simpa only [additionCurveChart, additionChartSpec, additionChartOutput,
      ordinaryIndex, ordinaryChartAddition, ordinaryInputRight, additionChartInclusion,
      ← Category.assoc, ← Spec.map_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      hr, CommRingCat.ofHom_comp] using h
  have reciprocal (b : Bool) :
      (modificationCenterSheaf W s).comap (additionCurveChart W (reciprocalIndex b)) ≤
        (modificationCenterSheaf W s).comap
          (additionChartInclusion W (reciprocalIndex b) ≫
            Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ≫
              integralCurveChart W 2) := by
    have h := modificationCenterSheaf_spec_le W s 1 2
      (reciprocalChartAddition W b) (reciprocalInputRight W b)
      (reciprocalSpecialization_center_le W s b (AlgHom.id R _) b3 b4 h3 h4)
    cases b <;>
      dsimp only [ordinaryIndex, reciprocalIndex, additionChartRing] at h ⊢ <;>
      simpa only [additionCurveChart, additionChartSpec, additionChartOutput,
      reciprocalIndex, reciprocalChartAddition, reciprocalInputRight, additionChartInclusion,
      ← Category.assoc, ← Spec.map_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      hr, CommRingCat.ofHom_comp] using h
  cases i
  · exact ordinary false
  · exact ordinary true
  · exact reciprocal false
  · exact reciprocal true

include h3 h4 in
/-- Every polynomial presentation preserves the same global ideal sheaf. -/
theorem projectiveAdditionChart_center_le (j k t : Fin 3) (b6 : R) (h6 : W.a₆ = s * b6) :
    (modificationCenterSheaf W s).comap
        (Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
          integralCurveChart W t) ≤
      (modificationCenterSheaf W s).comap
        (Spec.map (CommRingCat.ofHom ((additionOutputRestriction W j k t).comp
          (chartProductRight W j k)).toRingHom) ≫ integralCurveChart W k) :=
  modificationCenterSheaf_spec_le W s t k _ _
    (projectiveSpecialization_center_le W s j k t (AlgHom.id R _) b3 b4 b6 h3 h4 h6)

end FLT.Mazur.WeierstrassIntegralChart
