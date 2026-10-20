/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCrossDepthReciprocalTangentOutput
public import FLT.Mazur.WeierstrassChartCrossComparison
public import FLT.Mazur.WeierstrassFlatSectionRegular

/-!
# Cross-depth reciprocal/tangent comparison on arbitrary flat schemes

Global sections compare actual formulas over a common coefficient morphism.
Equality of the original cubic inputs suffices; the source need not be affine,
reduced, or contained in the original smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S']
  (W : WeierstrassCurve R) (s b3 b4 b6 t c3 c4 c6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (a₂ c₂ : Coordinate W t c3 c4 c6 →ₐ[R] S')
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (k3 : W.a₃ = t * c3) (k4 : W.a₄ = t * c4) (k6 : W.a₆ = t ^ 2 * c6)
local notation "T" => DividedReciprocalOutputRing W s b3 b4 b6 a c
local notation "V" => DividedTangentRing W t c3 c4 c6 a₂ c₂
local notation "Q" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "j" => (IsScalarTower.toAlgHom R Q T).comp (IsScalarTower.toAlgHom R S Q)
local notation "j₂" => IsScalarTower.toAlgHom R S' V
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6
local notation "orig₂" => fromOriginal W t c3 c4 c6 k3 k4 k6
local notation "a₀" => ((j).comp a).comp orig
local notation "c₀" => ((j).comp c).comp orig
local notation "a₀₂" => ((j₂).comp a₂).comp orig₂
local notation "c₀₂" => ((j₂).comp c₂).comp orig₂

/-- Equal original inputs identify reciprocal and tangent outputs across divided depths. -/
theorem dividedCrossDepthReciprocalTangent_scheme {X : Scheme.{u}}
    (b : X ⟶ Spec (.of R)) [Flat b] (hs : IsRegular s)
    (f : X ⟶ Spec (.of T)) (g : X ⟶ Spec (.of V))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = b)
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap R V)) = b)
    (ha : f ≫ Spec.map (CommRingCat.ofHom (a₀).toRingHom) ≫ integralCurveChart W 2 =
      g ≫ Spec.map (CommRingCat.ofHom (a₀₂).toRingHom) ≫ integralCurveChart W 2)
    (hc : f ≫ Spec.map (CommRingCat.ofHom (c₀).toRingHom) ≫ integralCurveChart W 2 =
      g ≫ Spec.map (CommRingCat.ofHom (c₀₂).toRingHom) ≫ integralCurveChart W 2) :
    f ≫ dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 =
      g ≫ dividedTangentToCurve W t c3 c4 c6 a₂ c₂ k3 k4 k6 := by
  let _ := specSectionAlgebra b
  let e := specSectionAlgHom b f hf
  let v := specSectionAlgHom b g hg
  have ha' : e.comp a₀ = v.comp a₀₂ := by
    apply specSectionAlgHom_comp_eq b f g hf hg
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using ha
  have hc' : e.comp c₀ = v.comp c₀₂ := by
    apply specSectionAlgHom_comp_eq b f g hf hg
    apply (cancel_mono (integralCurveChart W 2)).mp
    simpa only [Category.assoc] using hc
  have hr : IsRegular (algebraMap R Γ(X, ⊤) s) := specSectionHom_isRegular b hs
  have ho := dividedCrossDepthReciprocalTangentOutput_scaled
    W s b3 b4 b6 t c3 c4 c6 a c a₂ c₂ h3 h4 h6 k3 k4 k6 e v ha' hc' hr
  let A := dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6
  let C := dividedTangentOutput W t c3 c4 c6 a₂ c₂ k3 k4 k6
  change (f ≫ Spec.map (CommRingCat.ofHom A.toRingHom)) ≫ integralCurveChart W 1 =
    (g ≫ Spec.map (CommRingCat.ofHom C.toRingHom)) ≫ integralCurveChart W 2
  apply global_eq_of_chart_cross W 1 2
  · simp only [Category.assoc, chartStructure, specAlgHom_structure, hf, hg]
  · intro i
    simp only [specSectionHom_comp, RingHom.comp_apply]
    change (e.comp A) (coord W 1 i) =
      (e.comp A) (coord W 1 2) * (v.comp C) (coord W 2 i)
    rw [ho i, ho 2]
    simp only [coord_self, map_one, mul_one, C]

end FLT.Mazur.WeierstrassDilatation
