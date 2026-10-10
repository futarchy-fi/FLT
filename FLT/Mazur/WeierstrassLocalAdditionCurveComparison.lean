/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineAdditionGluing
public import FLT.Mazur.WeierstrassInfinityTransportedScheme
public import FLT.Mazur.WeierstrassInfinityOverlapScheme
public import FLT.Mazur.WeierstrassInfinityOutputComparison

/-!
# Curve-valued comparison of the local addition laws

The existing output-overlap factorizations identify the actual local morphisms
into the glued cubic on arbitrary common input schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Transported affine laws agree whenever their original input maps agree. -/
theorem transportedAffine_curve_eq (j k : Fin 3) (i l : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (affineOverlapAdditionCover W j k hΔ).X i)
    (g : X ⟶ (affineOverlapAdditionCover W j k hΔ).X l)
    (h : f ≫ transportedPolynomialDomainMap W j k i hΔ =
      g ≫ transportedPolynomialDomainMap W j k l hΔ) :
    f ≫ affineOverlapAdditionSpec W j k hΔ i ≫ integralCurveChart W (additionChartOutput i) =
      g ≫ affineOverlapAdditionSpec W j k hΔ l ≫
        integralCurveChart W (additionChartOutput l) := by
  have hi : f ≫ (affineOverlapAdditionCover W j k hΔ).f i =
      g ≫ (affineOverlapAdditionCover W j k hΔ).f l := by
    apply (cancel_mono (Spec.map
      (CommRingCat.ofHom (productOverlapRestriction W j k 2 2).toRingHom))).mp
    simpa only [transportedPolynomialDomainMap, Category.assoc] using h
  rw [← affineOverlapAdditionSpec_glued, ← affineOverlapAdditionSpec_glued,
    ← Category.assoc f, hi, Category.assoc]

/-- Transported affine and polynomial addition agree on every common input scheme. -/
theorem transportedPolynomial_curve_eq (j k : Fin 3) (i : AdditionChartIndex) (t : Fin 3)
    {X : Scheme.{u}} (f : X ⟶ (affineOverlapAdditionCover W j k hΔ).X i)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W j k t)))
    (h : f ≫ transportedPolynomialDomainMap W j k i hΔ =
      g ≫ projectiveAdditionInclusion W j k t) :
    f ≫ affineOverlapAdditionSpec W j k hΔ i ≫ integralCurveChart W (additionChartOutput i) =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
        integralCurveChart W t := by
  have he := integralCurve_output_eq W t (additionChartOutput i) _ _
    (transportedPolynomialSchemeOutput W j k i t hΔ)
    (transportedPolynomialSchemeOutput_polynomial W j k i t hΔ)
    (transportedPolynomialSchemeOutput_affine W j k i t hΔ)
  have hh := congrArg (fun a => pullback.lift f g h ≫ a) he.symm
  simpa only [projectiveAdditionInclusion, infinityAdditionInclusion, infinityAdditionSpec,
    Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hh

/-- Transported affine and infinity addition agree on the full common domain. -/
theorem transportedInfinity_curve_eq (i : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (affineOverlapAdditionCover W 1 1 hΔ).X i)
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ transportedPolynomialDomainMap W 1 1 i hΔ = g ≫ infinityAdditionInclusion W) :
    f ≫ affineOverlapAdditionSpec W 1 1 hΔ i ≫ integralCurveChart W (additionChartOutput i) =
      g ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  have he := integralCurve_output_eq W (additionChartOutput i) 1 _ _
    (infinityTransportedSchemeOutput W i hΔ)
    (infinityTransportedSchemeOutput_affine W i hΔ)
    (infinityTransportedSchemeOutput_infinity W i hΔ)
  have hh := congrArg (fun a => pullback.lift f g h ≫ a) he
  simpa only [projectiveAdditionInclusion, infinityAdditionInclusion, infinityAdditionSpec,
    Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hh

/-- Infinity and polynomial addition have the same image in the glued cubic. -/
theorem infinityPolynomial_curve_eq (t : Fin 3) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (g : X ⟶ Spec (.of (AdditionOutputOpen W 1 1 t)))
    (h : f ≫ infinityAdditionInclusion W = g ≫ projectiveAdditionInclusion W 1 1 t) :
    f ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 t).toRingHom) ≫
        integralCurveChart W t := by
  have he :
      (Spec.map (CommRingCat.ofHom (infinityProjectivePolynomial W t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 t).toRingHom)) ≫
          integralCurveChart W t =
      (Spec.map (CommRingCat.ofHom
        (S := InfinityProjectiveOverlap W t) (infinityProjectiveRestriction W t).toRingHom) ≫
        infinityAdditionSpec W) ≫ integralCurveChart W 1 := by
    apply integralCurve_output_eq W t 1 _ _
      (Spec.map (CommRingCat.ofHom (infinityPolynomialOutputLift W t).toRingHom))
    · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun a : Coordinate W t →ₐ[R] InfinityProjectiveOverlap W t =>
        Spec.map (CommRingCat.ofHom (R := Coordinate W t)
          (S := InfinityProjectiveOverlap W t) a.toRingHom))
        (infinityPolynomialOutputLift_restriction W t)
    · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg (fun a : Coordinate W 1 →ₐ[R] InfinityProjectiveOverlap W t =>
        Spec.map (CommRingCat.ofHom (R := Coordinate W 1)
          (S := InfinityProjectiveOverlap W t) a.toRingHom))
        (infinityPolynomialOutputLift_transition W t)
  have hh := congrArg (fun a => (infinityProjective_isPullback W t).lift f g h ≫ a) he.symm
  simpa only [Category.assoc, IsPullback.lift_fst_assoc, IsPullback.lift_snd_assoc] using hh

end FLT.Mazur.WeierstrassIntegralChart
