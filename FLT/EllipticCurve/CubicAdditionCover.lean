/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicVerticalAddition

/-! # An open cover of the affine input product for addition

The secant, nonvertical tangent, and two vertical chord domains cover the
ordinary affine chart product when the discriminant is invertible.
This supplies the source cover; compatibility of every pair of addition
morphisms and inputs outside the ordinary chart remain separate steps. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Chord denominators commute with extension of coefficients. -/
theorem chordDenominator_baseChange {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (x₂ y₁ y₂ : S) :
    f (chordDenominator (W.map (algebraMap R S)) x₂ y₁ y₂) =
      chordDenominator (W.map (algebraMap R T)) (f x₂) (f y₁) (f y₂) := by
  simp [chordDenominator, WeierstrassCurve.map]

/-- Divided differences commute with extension of coefficients. -/
theorem chordNumerator_baseChange {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (x₁ x₂ y₁ : S) :
    f (chordNumerator (W.map (algebraMap R S)) x₁ x₂ y₁) =
      chordNumerator (W.map (algebraMap R T)) (f x₁) (f x₂) (f y₁) := by
  simp [chordNumerator, WeierstrassCurve.map]

/-- The homogeneous output coordinate commutes with extension of coefficients. -/
theorem chordY_baseChange {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : S →ₐ[R] T) (x₁ x₂ y₁ s t : S) :
    f (chordY (W.map (algebraMap R S)) x₁ x₂ y₁ s t) =
      chordY (W.map (algebraMap R T)) (f x₁) (f x₂) (f y₁) (f s) (f t) := by
  simp [chordY, chordXNumerator, WeierstrassCurve.map]


/-- The four principal-open denominators for addition on the affine input product. -/
def additionDenominator : Fin 4 → AffinePairRing W :=
  ![secantDenominator W, tangentDenominator W, pairChordY W false, pairChordY W true]


private theorem span_range_eq_top_of_field_points {A : Type u} [CommRing A] [Algebra R A]
    (d : Fin 4 → A)
    (h : ∀ (K : Type u) [Field K] [Algebra R K] (f : A →ₐ[R] K), ∃ i, f (d i) ≠ 0) :
    Ideal.span (Set.range d) = ⊤ := by
  by_contra ht
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ ht
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  obtain ⟨i, hi⟩ := h (A ⧸ m) (Ideal.Quotient.mkₐ R m)
  exact hi (Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨i, rfl⟩)))

/-- Smoothness guarantees that these four domains cover the whole affine input product. -/
theorem addition_denominators_span [W.IsElliptic] :
    Ideal.span (Set.range (additionDenominator W)) = ⊤ := by
  apply span_range_eq_top_of_field_points (R := R) (A := AffinePairRing W)
    (additionDenominator W)
  intro K _ _ f
  let E := W.map (algebraMap R K)
  have he : E.toAffine.Equation (f (pairCoord W false 0)) (f (pairCoord W false 1)) :=
    chart_hom_equation W (f.comp (pairInput W false))
  have hn := (Affine.equation_iff_nonsingular (W := E.toAffine)).mp he
  have hx : f (secantDenominator W) =
      f (pairCoord W true 0) - f (pairCoord W false 0) := by
    have h := map_sub f (pairCoord W true 0) (pairCoord W false 0)
    exact h
  have ht : f (tangentDenominator W) =
      chordDenominator E (f (pairCoord W true 0)) (f (pairCoord W false 1))
        (f (pairCoord W true 1)) :=
    chordDenominator_baseChange W (S := AffinePairRing W) (T := K) f
      (pairCoord W true 0) (pairCoord W false 1) (pairCoord W true 1)
  have hs₀ : f (pairChordS W false) =
      f (pairCoord W true 1) - f (pairCoord W false 1) := by
    have h := map_sub f (pairCoord W true 1) (pairCoord W false 1)
    exact h
  have ht₀ : f (pairChordT W false) =
      f (pairCoord W true 0) - f (pairCoord W false 0) := hx
  have hs₁ : f (pairChordS W true) =
      chordNumerator E (f (pairCoord W false 0)) (f (pairCoord W true 0))
        (f (pairCoord W false 1)) :=
    chordNumerator_baseChange W (S := AffinePairRing W) (T := K) f
      (pairCoord W false 0) (pairCoord W true 0) (pairCoord W false 1)
  have ht₁ : f (pairChordT W true) =
      chordDenominator E (f (pairCoord W true 0)) (f (pairCoord W false 1))
        (f (pairCoord W true 1)) := ht
  have hy₀ := chordY_baseChange W f (pairCoord W false 0) (pairCoord W true 0)
    (pairCoord W false 1) (pairChordS W false) (pairChordT W false)
  have hy₁ := chordY_baseChange W f (pairCoord W false 0) (pairCoord W true 0)
    (pairCoord W false 1) (pairChordS W true) (pairChordT W true)
  rw [hs₀, ht₀] at hy₀
  rw [hs₁, ht₁] at hy₁
  rcases chord_domains_cover E (x₂ := f (pairCoord W true 0))
      (y₂ := f (pairCoord W true 1)) hn with hc | hc | hc | hc
  · exact ⟨0, fun hz ↦ hc (hx.symm.trans hz)⟩
  · exact ⟨1, fun hz ↦ hc (ht.symm.trans hz)⟩
  · exact ⟨2, fun hz ↦ hc (hy₀.symm.trans hz)⟩
  · exact ⟨3, fun hz ↦ hc (hy₁.symm.trans hz)⟩

/-- Each of the four principal opens, as an affine scheme. -/
def affineAdditionOpen (i : Fin 4) : Scheme.{u} :=
  Spec (.of (Localization.Away (additionDenominator W i)))

/-- Inclusion of an addition domain into the affine input product. -/
def affineAdditionInclusion (i : Fin 4) :
    affineAdditionOpen W i ⟶ Spec (.of (AffinePairRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (AffinePairRing W) (Localization.Away (additionDenominator W i))))

instance affineAdditionInclusion_isOpenImmersion (i : Fin 4) :
    IsOpenImmersion (affineAdditionInclusion W i) :=
  IsOpenImmersion.of_isLocalization (additionDenominator W i)

/-- The scheme-theoretic cover by the four domains of the existing local addition maps. -/
def affineAdditionCover [W.IsElliptic] : (Spec (.of (AffinePairRing W))).OpenCover where
  I₀ := Fin 4
  X := affineAdditionOpen W
  f := affineAdditionInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hi : ∃ i, additionDenominator W i ∉ x.asIdeal := by
      by_contra h
      push Not at h
      apply x.isPrime.ne_top
      apply top_unique
      rw [← addition_denominators_span W]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hr := PrimeSpectrum.localization_away_comap_range
      (Localization.Away (additionDenominator W i)) (additionDenominator W i)
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr hi
    exact ⟨i, y, hy⟩

end WeierstrassCurve.CubicCharts
