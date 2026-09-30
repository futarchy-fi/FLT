/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveProductChartCover
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Change of coefficients on projective space

An arbitrary coefficient homomorphism induces a morphism of polynomial Proj
schemes. Standard charts pull back to standard charts, and their ring maps
send scalars through the coefficient homomorphism and preserve coordinate ratios.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

universe u v

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.ProjectiveSpace

variable {R S : Type (max u v)} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type v)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient change preserves the standard polynomial grading. -/
def coefficientGradedMap : grading R ι →+*ᵍ grading S ι where
  __ := MvPolynomial.map φ
  map_mem := fun h ↦ h.map φ

@[simp]
lemma coefficientGradedMap_apply (p : MvPolynomial ι R) :
    coefficientGradedMap φ ι p = MvPolynomial.map φ p := rfl

/-- The image of the irrelevant ideal contains every positive-degree polynomial. -/
lemma coefficientGradedMap_irrelevant :
    HomogeneousIdeal.irrelevant (grading S ι) ≤
      (HomogeneousIdeal.irrelevant (grading R ι)).map (coefficientGradedMap φ ι) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  have hspan : Ideal.span (Set.range (X : ι → MvPolynomial ι S)) ≤
      (HomogeneousIdeal.irrelevant (grading R ι)).toIdeal.map
        (coefficientGradedMap φ ι).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hX : X i ∈ (HomogeneousIdeal.irrelevant (grading R ι)).toIdeal :=
      HomogeneousIdeal.mem_irrelevant_of_mem (grading R ι) (by decide : 0 < 1)
        (isHomogeneous_X R i)
    have hm := Ideal.mem_map_of_mem (coefficientGradedMap φ ι).toRingHom hX
    change MvPolynomial.map φ (X i) ∈ _ at hm
    rw [MvPolynomial.map_X] at hm
    exact hm
  apply hspan
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro d hd
  by_contra h
  have hd0 : d = 0 := by
    ext i
    by_contra hi
    exact h ⟨i, Set.mem_univ i, hi⟩
  subst d
  exact (mem_support_iff.mp hd) (hp.coeff_eq_zero (by simpa using hn.ne))

/-- The actual projective-space morphism induced by a coefficient homomorphism. -/
def coefficientMap : space S ι ⟶ space R ι :=
  Proj.map (coefficientGradedMap φ ι) (coefficientGradedMap_irrelevant φ ι)

/-- Coefficient change pulls back each standard chart to its namesake. -/
@[simp]
lemma coefficientMap_preimage_chart (i : ι) :
    coefficientMap φ ι ⁻¹ᵁ chart R ι i = chart S ι i := by
  change Proj.basicOpen _ (coefficientGradedMap φ ι (X i)) = _
  simp [chart]

/-- The induced homomorphism of homogeneous localization chart rings. -/
def coefficientChartRingMap (i : ι) : chartRing R ι i →+* chartRing S ι i :=
  HomogeneousLocalization.map (coefficientGradedMap φ ι) (by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩)

/-- Coordinate ratios are unchanged by coefficient extension. -/
@[simp]
lemma coefficientChartRingMap_coordinate (i j : ι) :
    coefficientChartRingMap φ ι i (coordinate R ι i j) = coordinate S ι i j := by
  apply val_injective
  simp [coefficientChartRingMap, coordinate, Away.mk, HomogeneousLocalization.map_mk]

/-- Scalars are sent through the original ring homomorphism. -/
@[simp]
lemma coefficientChartRingMap_scalar (i : ι) (r : R) :
    coefficientChartRingMap φ ι i (chartScalars R ι i r) = chartScalars S ι i (φ r) := by
  apply val_injective
  simp [coefficientChartRingMap, chartScalars, constantsToZero,
    fromZeroRingHom, HomogeneousLocalization.map_mk]

/-- On a standard chart the scheme map is the spectrum of the localization map. -/
@[reassoc]
lemma chartMap_coefficientMap (i : ι) :
    chartMap S ι i ≫ coefficientMap φ ι =
      Spec.map (CommRingCat.ofHom (coefficientChartRingMap φ ι i)) ≫ chartMap R ι i := by
  have h (s : MvPolynomial ι S) (hs : coefficientGradedMap φ ι (X i) = s)
      (hm : s ∈ grading S ι 1) :
      Proj.awayι (grading S ι) s hm (by decide) ≫ coefficientMap φ ι =
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.map (coefficientGradedMap φ ι)
            (P := Submonoid.powers (X i)) (Q := Submonoid.powers s) (by
              rintro _ ⟨n, rfl⟩
              exact ⟨n, by simp [← hs]⟩))) ≫ chartMap R ι i := by
    subst s
    exact Proj.awayι_comp_map (coefficientGradedMap φ ι)
      (coefficientGradedMap_irrelevant φ ι) (by decide) (X i) (isHomogeneous_X R i)
  exact h (X i) (by simp) (isHomogeneous_X S i)

/-- The projective morphism lies over the spectrum map of coefficients. -/
@[reassoc]
lemma coefficientMap_baseProjection :
    coefficientMap φ ι ≫ baseProjection R ι =
      baseProjection S ι ≫ Spec.map (CommRingCat.ofHom φ) := by
  apply (standardChartCover S ι).hom_ext
  intro i
  change chartMap S ι i ≫ _ = chartMap S ι i ≫ _
  rw [chartMap_coefficientMap_assoc, chartMap_baseProjection,
    chartMap_baseProjection_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact coefficientChartRingMap_scalar φ ι i

end FLT.Mazur.ProjectiveSpace
