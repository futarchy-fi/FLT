/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveIdentity
public import FLT.EllipticCurve.CubicAffineAddition

/-! # A cover of infinity-chart times affine-chart for addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Z-coordinate of the first input on infinity-chart times affine-chart. -/
def mixedFirstZ : ChartPairRing W true false :=
  (Algebra.TensorProduct.includeLeft :
    Ring W true →ₐ[R] ChartPairRing W true false) (coord W true 1)

/-- Denominators for the affine-input and projective-addition pieces of the mixed chart. -/
def mixedAdditionDenominator : Fin 2 → ChartPairRing W true false :=
  ![mixedFirstZ W, projectiveAdditionDenominator W true false false]

theorem mixedAddition_field_cover {K : Type u} [Field K] [Algebra R K]
    (f : ChartPairRing W true false →ₐ[R] K) :
    f (mixedFirstZ W) ≠ 0 ∨
      f (projectiveAdditionDenominator W true false false) ≠ 0 := by
  by_cases hz : f (mixedFirstZ W) = 0
  · right
    let a : Ring W true →ₐ[R] K := f.comp Algebra.TensorProduct.includeLeft
    let b : Ring W false →ₐ[R] K := f.comp Algebra.TensorProduct.includeRight
    have hp := chartPointCoords_equation W true a
    have hu : a (coord W true 0) = 0 :=
      Projective.X_eq_zero_of_Z_eq_zero hp hz
    have hl : f ∘ chartPairLeft W true false = ![0, 1, 0] := by
      ext i
      fin_cases i
      · exact hu
      · exact f.map_one
      · exact hz
    have hr : f ∘ chartPairRight W true false =
        ![b (coord W false 0), b (coord W false 1), 1] := by
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact f.map_one
    have h := Projective.baseChange_addXYZ (W' := W.toProjective) f
      (chartPairLeft W true false) (chartPairRight W true false)
    rw [hl, hr, projective_addXYZ_zero_left] at h
    have hd : f (projectiveAdditionDenominator W true false false) = 1 :=
      (congrFun h 2).symm
    rw [hd]
    exact one_ne_zero
  · exact Or.inl hz

private theorem two_denominators_span {A : Type u} [CommRing A] [Algebra R A]
    (d : Fin 2 → A)
    (h : ∀ (K : Type u) [Field K] [Algebra R K] (f : A →ₐ[R] K), ∃ i, f (d i) ≠ 0) :
    Ideal.span (Set.range d) = ⊤ := by
  by_contra ht
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ ht
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  obtain ⟨i, hi⟩ := h (A ⧸ m) (Ideal.Quotient.mkₐ R m)
  exact hi (Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨i, rfl⟩)))

theorem mixedAddition_denominators_span :
    Ideal.span (Set.range (mixedAdditionDenominator W)) = ⊤ := by
  apply two_denominators_span (R := R) (A := ChartPairRing W true false)
  intro K _ _ f
  rcases mixedAddition_field_cover W f with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- Principal-open pieces covering the mixed input chart. -/
def mixedAdditionOpen (i : Fin 2) : Scheme.{u} :=
  Spec (.of (Localization.Away (mixedAdditionDenominator W i)))

/-- Inclusion of a mixed addition piece into its input chart product. -/
def mixedAdditionInclusion (i : Fin 2) :
    mixedAdditionOpen W i ⟶ Spec (.of (ChartPairRing W true false)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (ChartPairRing W true false)
      (Localization.Away (mixedAdditionDenominator W i))))

instance mixedAdditionInclusion_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (mixedAdditionInclusion W i) :=
  IsOpenImmersion.of_isLocalization (mixedAdditionDenominator W i)

/-- The old affine-input region and the new projective region cover the mixed chart. -/
def mixedAdditionCover : (Spec (.of (ChartPairRing W true false))).OpenCover where
  I₀ := Fin 2
  X := mixedAdditionOpen W
  f := mixedAdditionInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hi : ∃ i, mixedAdditionDenominator W i ∉ x.asIdeal := by
      by_contra h
      push Not at h
      apply x.isPrime.ne_top
      apply top_unique
      rw [← mixedAddition_denominators_span W]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hr := PrimeSpectrum.localization_away_comap_range
      (Localization.Away (mixedAdditionDenominator W i)) (mixedAdditionDenominator W i)
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr hi
    exact ⟨i, y, hy⟩

end WeierstrassCurve.CubicCharts
