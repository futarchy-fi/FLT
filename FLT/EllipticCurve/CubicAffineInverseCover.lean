/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAffineCommutativity

/-! # A cover of the inverse graph by the two vertical addition domains -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Pullback on functions for the graph P ↦ (P,-P) on the ordinary input chart. -/
def inversePair : AffinePairRing W →ₐ[R] Ring W false :=
  Algebra.TensorProduct.productMap (AlgHom.id R _) (affineNegationEquiv W).toAlgHom

@[simp] theorem inversePair_coord_left (i : Fin 2) :
    inversePair W (pairCoord W false i) = coord W false i :=
  DFunLike.congr_fun (Algebra.TensorProduct.productMap_left
    (AlgHom.id R (Ring W false)) (affineNegationEquiv W).toAlgHom) (coord W false i)

@[simp] theorem inversePair_coord_right (i : Fin 2) :
    inversePair W (pairCoord W true i) = affineNegationEquiv W (coord W false i) :=
  DFunLike.congr_fun (Algebra.TensorProduct.productMap_right
    (AlgHom.id R (Ring W false)) (affineNegationEquiv W).toAlgHom) (coord W false i)

@[simp] theorem inversePair_secantDenominator : inversePair W (secantDenominator W) = 0 := by
  have h := map_sub (inversePair W) (pairCoord W true 0) (pairCoord W false 0)
  simp only [inversePair_coord_right, inversePair_coord_left,
    affineNegationEquiv_coord_zero, sub_self] at h
  exact h

@[simp] theorem inversePair_tangentDenominator : inversePair W (tangentDenominator W) = 0 := by
  have h := chordDenominator_baseChange W (inversePair W)
    (pairCoord W true 0) (pairCoord W false 1) (pairCoord W true 1)
  simp only [inversePair_coord_right, inversePair_coord_left,
    affineNegationEquiv_coord_zero, affineNegationEquiv_coord_one] at h
  change inversePair W (tangentDenominator W) = _ at h
  unfold chordDenominator WeierstrassCurve.map at h
  linear_combination h

@[simp] theorem inversePair_chordT (b : Bool) : inversePair W (pairChordT W b) = 0 := by
  cases b
  · exact inversePair_secantDenominator W
  · exact inversePair_tangentDenominator W

@[simp] theorem inversePair_chordX (b : Bool) : inversePair W (pairChordX W b) = 0 := by
  have h := chordX_baseChange W (inversePair W)
    (pairCoord W false 0) (pairCoord W true 0) (pairChordS W b) (pairChordT W b)
  rw [inversePair_chordT, chordX_vertical] at h
  exact h

/-- The two vertical output denominators restricted to the inverse graph. -/
def inverseAdditionDenominator (b : Bool) : Ring W false :=
  inversePair W (pairChordY W b)

theorem inverseAddition_denominators_span [W.IsElliptic] :
    Ideal.span (Set.range (inverseAdditionDenominator W)) = ⊤ := by
  apply top_unique
  have hall := congrArg (Ideal.map (inversePair W).toRingHom) (addition_denominators_span W)
  rw [Ideal.map_span, Ideal.map_top] at hall
  rw [← hall]
  apply Ideal.span_le.mpr
  rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · change inversePair W (secantDenominator W) ∈ _
    rw [inversePair_secantDenominator]
    exact Ideal.zero_mem _
  · change inversePair W (tangentDenominator W) ∈ _
    rw [inversePair_tangentDenominator]
    exact Ideal.zero_mem _
  · exact Ideal.subset_span ⟨false, rfl⟩
  · exact Ideal.subset_span ⟨true, rfl⟩

/-- A vertical addition domain on the inverse graph. -/
abbrev InverseAdditionRing (b : Bool) := Localization.Away (inverseAdditionDenominator W b)

/-- Restriction of the inverse graph's input to one vertical domain. -/
def inverseAdditionRestriction (b : Bool) : Ring W false →ₐ[R] InverseAdditionRing W b :=
  IsScalarTower.toAlgHom R (Ring W false) (InverseAdditionRing W b)

/-- Inclusion of an open on which the inverse sum can be computed vertically. -/
def inverseAdditionInclusion (b : Bool) :
    Spec (.of (InverseAdditionRing W b)) ⟶ chart W false :=
  Spec.map (CommRingCat.ofHom (algebraMap (Ring W false) (InverseAdditionRing W b)))

instance inverseAdditionInclusion_isOpenImmersion (b : Bool) :
    IsOpenImmersion (inverseAdditionInclusion W b) :=
  IsOpenImmersion.of_isLocalization (inverseAdditionDenominator W b)

/-- The vertical secant and tangent domains cover every inverse pair. -/
def inverseAdditionCover [W.IsElliptic] : (chart W false).OpenCover where
  I₀ := Bool
  X b := Spec (.of (InverseAdditionRing W b))
  f := inverseAdditionInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hi : ∃ b, inverseAdditionDenominator W b ∉ x.asIdeal := by
      by_contra h
      push Not at h
      apply x.isPrime.ne_top
      apply top_unique
      rw [← inverseAddition_denominators_span W]
      apply Ideal.span_le.mpr
      rintro _ ⟨b, rfl⟩
      exact h b
    obtain ⟨b, hb⟩ := hi
    have hr := PrimeSpectrum.localization_away_comap_range
      (InverseAdditionRing W b) (inverseAdditionDenominator W b)
    obtain ⟨y, hy⟩ := (Set.ext_iff.mp hr x).mpr hb
    exact ⟨b, y, hy⟩

end WeierstrassCurve.CubicCharts
