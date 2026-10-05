/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smoothness of the proper Weierstrass scheme

The affine chart is covered by its derivative opens when the discriminant
is invertible. The infinity chart is covered by its overlap with the affine
chart and the open where its transverse derivative is invertible. Explicit
submersive presentations prove smoothness on these opens, hence globally.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open Algebra

set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A partial derivative of the chart equation, in its quotient coordinate ring. -/
def derivative (b : Bool) (i : Fin 2) : Ring W b :=
  Ideal.Quotient.mk _ (pderiv i (equation W b))

/-- The one-relation chart presentation, with the chosen Jacobian column. -/
def chartPresentation (b : Bool) (i : Fin 2) :
    PreSubmersivePresentation R (Ring W b) (Fin 2) Unit :=
  (PreSubmersivePresentation.naive (v := fun _ : Unit ↦ equation W b)
    (fun _ ↦ i) (Function.injective_of_subsingleton _)).ofAlgEquiv
      (Ideal.quotientEquivAlgOfEq R (by simp))

/-- The Jacobian of the chosen presentation is precisely its partial derivative. -/
theorem chartPresentation_jacobian (b : Bool) (i : Fin 2) :
    (chartPresentation W b i).jacobian = derivative W b i := by
  rw [chartPresentation, PreSubmersivePresentation.jacobian_ofAlgEquiv,
    PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    PreSubmersivePresentation.jacobiMatrix_naive]
  change Ideal.quotientEquivAlgOfEq R _ (Ideal.Quotient.mk _ _) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The localization of a chart at a partial derivative. -/
abbrev DerivativeRing (b : Bool) (i : Fin 2) := Localization.Away (derivative W b i)

/-- Inverting the chosen partial derivative makes the chart standard smooth. -/
instance derivativeRing_isStandardSmooth (b : Bool) (i : Fin 2) :
    IsStandardSmooth R (DerivativeRing W b i) := by
  let P := chartPresentation W b i
  let Q := PreSubmersivePresentation.localizationAway (DerivativeRing W b i) (derivative W b i)
  have hd : IsUnit (algebraMap (Ring W b) (DerivativeRing W b i) (derivative W b i)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let S : SubmersivePresentation R (DerivativeRing W b i) _ _ :=
    { toPreSubmersivePresentation := Q.comp P
      jacobian_isUnit := by
        simpa [Q, P, Algebra.smul_def, chartPresentation_jacobian, -isUnit_map_iff]
          using hd.mul hd }
  exact S.isStandardSmooth

/-- These actual localized coordinate algebras are smooth over the coefficient base. -/
instance derivativeRing_smooth (b : Bool) (i : Fin 2) :
    Algebra.Smooth R (DerivativeRing W b i) := inferInstance

/-- Evaluation at the universal affine coordinates is the quotient map. -/
theorem eval₂_coord {S : Type*} [CommRing S] (b : Bool) (f : Ring W b →+* S)
    (p : MvPolynomial (Fin 2) R) :
    eval₂ (f.comp (algebraMap R (Ring W b))) (fun i ↦ f (coord W b i)) p =
      f (Ideal.Quotient.mk _ p) := by
  have h : eval₂Hom (f.comp (algebraMap R (Ring W b))) (fun i ↦ f (coord W b i)) =
      f.comp (Ideal.Quotient.mk (Ideal.span {equation W b})) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [eval₂Hom_C]
      rfl
    · intro i
      rw [eval₂Hom_X']
      rfl
  exact DFunLike.congr_fun h p

/-- Every algebra-valued point satisfies its defining chart equation. -/
theorem eval₂_coord_equation {S : Type*} [CommRing S] (b : Bool) (f : Ring W b →+* S) :
    eval₂ (f.comp (algebraMap R (Ring W b))) (fun i ↦ f (coord W b i))
      (equation W b) = 0 := by
  rw [eval₂_coord, Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-- The x derivative on the ordinary affine chart. -/
theorem derivative_affine_zero :
    derivative W false 0 = algebraMap R _ W.a₁ * coord W false 1 -
      (3 * coord W false 0 ^ 2 + 2 * algebraMap R _ W.a₂ * coord W false 0 +
        algebraMap R _ W.a₄) := by
  have hp : pderiv 0 (equation W false) =
      C W.a₁ * X 1 - (3 * X 0 ^ 2 + 2 * C W.a₂ * X 0 + C W.a₄) := by
    simp [equation]
    ring
  unfold derivative
  rw [hp]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
  rfl

/-- The y derivative on the ordinary affine chart. -/
theorem derivative_affine_one :
    derivative W false 1 =
      2 * coord W false 1 + algebraMap R _ W.a₁ * coord W false 0 + algebraMap R _ W.a₃ := by
  have hp : pderiv 1 (equation W false) = 2 * X 1 + C W.a₁ * X 0 + C W.a₃ := by
    simp [equation]
  unfold derivative
  rw [hp]
  simp only [map_add, map_mul, map_ofNat]
  rfl

/-- Invertible discriminant excludes simultaneous vanishing of the affine derivatives. -/
theorem affine_derivatives_span [W.IsElliptic] :
    Ideal.span (Set.range (derivative W false)) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let := hm
  let f : Ring W false →+* Ring W false ⧸ m := Ideal.Quotient.mk m
  let g : R →+* Ring W false ⧸ m := f.comp (algebraMap R _)
  let E : Affine (Ring W false ⧸ m) := (W.map g).toAffine
  have he : E.Equation (f (coord W false 0)) (f (coord W false 1)) := by
    have h := eval₂_coord_equation W (S := Ring W false ⧸ m) false f
    simpa [E, g, equation, Affine.equation_iff, WeierstrassCurve.map, sub_eq_zero] using h
  have hn := (Affine.equation_iff_nonsingular (W := E)).mp he
  have hd (i : Fin 2) : f (derivative W false i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨i, rfl⟩))
  have h₀ := hd 0
  have h₁ := hd 1
  rw [derivative_affine_zero] at h₀
  rw [derivative_affine_one] at h₁
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h₀ h₁
  rcases (Affine.nonsingular_iff' _ _).mp hn with ⟨_, hn | hn⟩
  · exact hn h₀
  · exact hn h₁

/-- The ordinary affine chart algebra is smooth when the discriminant is a unit. -/
instance affineRing_smooth [W.IsElliptic] : Algebra.Smooth R (Ring W false) := by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.ofLocalizationSpanTarget (algebraMap R _)
    (Set.range (derivative W false)) (affine_derivatives_span W)
  rintro ⟨r, ⟨i, rfl⟩⟩
  rw [← IsScalarTower.algebraMap_eq]
  exact RingHom.smooth_algebraMap.mpr (derivativeRing_smooth W false i)

/-- The derivative transverse to the infinity section. -/
theorem derivative_infinity_one :
    derivative W true 1 =
      1 + algebraMap R _ W.a₁ * coord W true 0 +
        2 * algebraMap R _ W.a₃ * coord W true 1 -
        (algebraMap R _ W.a₂ * coord W true 0 ^ 2 +
          2 * algebraMap R _ W.a₄ * coord W true 0 * coord W true 1 +
          3 * algebraMap R _ W.a₆ * coord W true 1 ^ 2) := by
  have hp : pderiv 1 (equation W true) =
      1 + C W.a₁ * X 0 + 2 * C W.a₃ * X 1 -
        (C W.a₂ * X 0 ^ 2 + 2 * C W.a₄ * X 0 * X 1 + 3 * C W.a₆ * X 1 ^ 2) := by
    simp [equation, InfinityChart.equation]
    ring
  unfold derivative
  rw [hp]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_one]
  rfl

/-- The overlap coordinate and transverse derivative cover the infinity chart. -/
theorem infinity_smooth_span :
    Ideal.span ({coord W true 1, derivative W true 1} : Set (Ring W true)) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let := hm
  let K := Ring W true ⧸ m
  let : Field K := Ideal.Quotient.field m
  let f : Ring W true →+* K := Ideal.Quotient.mk m
  have hv : f (coord W true 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hd : f (derivative W true 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have he := eval₂_coord_equation W (S := K) true f
  have hu : f (coord W true 0) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 3)
    simpa [equation, InfinityChart.equation, hv] using he
  rw [derivative_infinity_one] at hd
  simp [map_sub, map_add, map_mul, map_pow, hv, hu] at hd

/-- The infinity overlap is smooth by its explicit isomorphism with the affine overlap. -/
instance infinityOverlap_smooth [W.IsElliptic] : Algebra.Smooth R (Overlap W true) := by
  have : Algebra.Smooth (Ring W false) (Overlap W false) :=
    Algebra.Smooth.of_isLocalization_Away (coord W false 1)
  have : Algebra.Smooth R (Overlap W false) := Algebra.Smooth.comp R (Ring W false) _
  exact Algebra.Smooth.of_equiv (overlapEquiv W)

/-- The whole infinity chart algebra is smooth for an elliptic equation. -/
instance infinityRing_smooth [W.IsElliptic] : Algebra.Smooth R (Ring W true) := by
  apply RingHom.smooth_algebraMap.mp
  apply RingHom.Smooth.ofLocalizationSpanTarget (algebraMap R _)
    {coord W true 1, derivative W true 1} (infinity_smooth_span W)
  rintro ⟨r, hr⟩
  rcases hr with rfl | hr
  · rw [← IsScalarTower.algebraMap_eq]
    exact RingHom.smooth_algebraMap.mpr (infinityOverlap_smooth W)
  · rcases Set.mem_singleton_iff.mp hr with rfl
    rw [← IsScalarTower.algebraMap_eq]
    exact RingHom.smooth_algebraMap.mpr (derivativeRing_smooth W true 1)

/-- Each affine chart projection is a smooth morphism of schemes. -/
instance chartToBase_smooth [W.IsElliptic] (b : Bool) : Smooth (chartToBase W b) := by
  have : Algebra.Smooth R (Ring W b) := by
    cases b
    · exact affineRing_smooth W
    · exact infinityRing_smooth W
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr this

/-- The two affine charts constitute an open cover of the glued scheme. -/
def sourceOpenCover : (scheme W).OpenCover where
  I₀ := Bool
  X := chart W
  f := sourceChart W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    rcases charts_cover W x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩

/-- With invertible discriminant, the actual proper Weierstrass scheme is smooth over its base. -/
instance toBase_smooth [W.IsElliptic] : Smooth (toBase W) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (sourceOpenCover W)
  intro b
  change Smooth (sourceChart W b ≫ toBase W)
  cases b
  · change Smooth (affineChart W ≫ toBase W)
    rw [affineChart_toBase]
    infer_instance
  · change Smooth (infinityChart W ≫ toBase W)
    rw [infinityChart_toBase]
    infer_instance

end WeierstrassCurve.CubicCharts
