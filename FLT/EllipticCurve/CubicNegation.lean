/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicBaseChangeGlobal
public import FLT.EllipticCurve.Negation

/-! # Local negation morphisms for the glued cubic

Negation is an involution on the ordinary affine chart. Near infinity it is
defined after inverting the transformed Y-coordinate; the span lemma supplies
the required refinement of the two-chart cover. Compatibility on that refined
intersection and global negation remain separate steps. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Coordinate-ring conjugation, viewed as an algebra involution over the base. -/
def coordinateNegationEquiv : W.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing :=
  { (Affine.CoordinateRing.negHom W.toAffine).restrictScalars R with
    invFun := Affine.CoordinateRing.negHom W.toAffine
    left_inv := Affine.CoordinateRing.negHom_negHom W.toAffine
    right_inv := Affine.CoordinateRing.negHom_negHom W.toAffine }

/-- Pullback by negation in the ordinary quotient chart. -/
def affineNegationEquiv : Ring W false ≃ₐ[R] Ring W false :=
  ((affineCoordinateRingEquiv W).trans (coordinateNegationEquiv W)).trans
    (affineCoordinateRingEquiv W).symm

@[simp] theorem affineCoordinateRingEquiv_affineNegation (x : Ring W false) :
    affineCoordinateRingEquiv W (affineNegationEquiv W x) =
      Affine.CoordinateRing.negHom W.toAffine (affineCoordinateRingEquiv W x) := by
  simp [affineNegationEquiv, coordinateNegationEquiv]

@[simp] theorem affineNegationEquiv_involutive (x : Ring W false) :
    affineNegationEquiv W (affineNegationEquiv W x) = x := by
  apply (affineCoordinateRingEquiv W).injective
  simp only [affineCoordinateRingEquiv_affineNegation, Affine.CoordinateRing.negHom_negHom]

@[simp] theorem affineCoordinateRingEquiv_coord_zero :
    affineCoordinateRingEquiv W (coord W false 0) =
      Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X) := by
  change Ideal.Quotient.mk _ (bivariateCoordinates (X 0)) = _
  rw [bivariateCoordinates_X_zero]
  rfl

@[simp] theorem affineNegationEquiv_coord_zero :
    affineNegationEquiv W (coord W false 0) = coord W false 0 := by
  apply (affineCoordinateRingEquiv W).injective
  simp only [affineCoordinateRingEquiv_affineNegation, affineCoordinateRingEquiv_coord_zero,
    Affine.CoordinateRing.negHom_mk, Polynomial.C_comp]

@[simp] theorem affineNegationEquiv_coord_one :
    affineNegationEquiv W (coord W false 1) =
      -coord W false 1 - algebraMap R (Ring W false) W.a₁ * coord W false 0 -
        algebraMap R (Ring W false) W.a₃ := by
  apply (affineCoordinateRingEquiv W).injective
  simp only [affineCoordinateRingEquiv_affineNegation, map_sub, map_neg, map_mul,
    AlgEquiv.commutes, affineCoordinateRingEquiv_coord_zero,
    affineCoordinateRingEquiv_coord_one, Affine.CoordinateRing.negHom_mk,
    Polynomial.X_comp, Affine.negPolynomial, map_sub, map_neg, map_add, map_mul]
  have hscalar (r : R) :
      Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C r)) =
        algebraMap R W.toAffine.CoordinateRing r := rfl
  simp only [hscalar]
  ring

/-- Negation is an actual automorphism of the ordinary affine chart. -/
def affineNegation : chart W false ⟶ chart W false :=
  Spec.map (CommRingCat.ofHom (affineNegationEquiv W).toRingHom)

instance affineNegation_isIso : IsIso (affineNegation W) := by
  change IsIso (Scheme.Spec.mapIso (affineNegationEquiv W).toRingEquiv.toCommRingCatIso.op).hom
  infer_instance

@[reassoc (attr := simp)] theorem affineNegation_involutive :
    affineNegation W ≫ affineNegation W = 𝟙 _ := by
  unfold affineNegation
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (affineNegationEquiv_involutive W)

@[reassoc (attr := simp)] theorem affineNegation_toBase :
    affineNegation W ≫ chartToBase W false = chartToBase W false := by
  unfold affineNegation chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (affineNegationEquiv W).commutes

/-- The transformed homogeneous Y-coordinate in the infinity chart. -/
def infinityNegationDenominator : Ring W true :=
  -1 - algebraMap R (Ring W true) W.a₁ * coord W true 0 -
    algebraMap R (Ring W true) W.a₃ * coord W true 1

/-- The ordinary chart and the locus where negation stays in the infinity chart cover. -/
theorem infinity_negation_span :
    Ideal.span ({coord W true 1, infinityNegationDenominator W} : Set (Ring W true)) =
      ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let := hm
  let K := Ring W true ⧸ m
  let : Field K := Ideal.Quotient.field m
  let f : Ring W true →+* K := Ideal.Quotient.mk m
  have hv : f (coord W true 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have hd : f (infinityNegationDenominator W) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  have he := eval₂_coord_equation W (S := K) true f
  have hu : f (coord W true 0) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 3)
    simpa [equation, InfinityChart.equation, hv] using he
  simp [infinityNegationDenominator, map_sub, map_mul, hv, hu] at hd

/-- The infinity formula for negation preserves the cubic wherever its denominator is invertible. -/
theorem infinity_negation_identity (u v t : R)
    (ht : t * (-1 - W.a₁ * u - W.a₃ * v) = 1) :
    eval ![u * t, v * t] (equation W true) = t ^ 3 * eval ![u, v] (equation W true) := by
  simp only [equation, ite_eq_left, InfinityChart.equation, map_sub, map_add, map_mul,
    map_pow, eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination v * t * (t - 1) * ht

/-- The infinity neighborhood where the negated Y-coordinate is invertible. -/
abbrev NegationNeighborhood := Localization.Away (infinityNegationDenominator W)

/-- The local infinity coordinates of the negated point. -/
def infinityNegationCoords (i : Fin 2) : NegationNeighborhood W :=
  algebraMap (Ring W true) (NegationNeighborhood W) (coord W true i) *
    IsLocalization.Away.invSelf (infinityNegationDenominator W)

theorem infinityNegationCoords_root :
    aeval (infinityNegationCoords W) (equation W true) = 0 := by
  let f := algebraMap (Ring W true) (NegationNeighborhood W)
  let t : NegationNeighborhood W := IsLocalization.Away.invSelf (infinityNegationDenominator W)
  have ht : t * (-1 - algebraMap R (NegationNeighborhood W) W.a₁ * f (coord W true 0) -
      algebraMap R (NegationNeighborhood W) W.a₃ * f (coord W true 1)) = 1 := by
    have h : t * f (infinityNegationDenominator W) = 1 := by
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (infinityNegationDenominator W)
    simpa only [f, infinityNegationDenominator, map_sub, map_neg, map_one, map_mul,
      ← IsScalarTower.algebraMap_apply R (Ring W true)] using h
  have h := infinity_negation_identity (W.map (algebraMap R (NegationNeighborhood W)))
    (f (coord W true 0)) (f (coord W true 1)) t ht
  rw [← map_equation W] at h
  simp only [eval_map] at h
  have he := eval₂_coord_equation W (S := NegationNeighborhood W) true f
  dsimp only [f] at he
  rw [← IsScalarTower.algebraMap_eq R (Ring W true) (NegationNeighborhood W)] at he
  have hv : ![f (coord W true 0), f (coord W true 1)] = fun i ↦ f (coord W true i) := by
    ext i
    fin_cases i <;> rfl
  rw [hv, he, mul_zero] at h
  have hc : ![f (coord W true 0) * t, f (coord W true 1) * t] =
      infinityNegationCoords W := by
    ext i
    fin_cases i <;> rfl
  rw [hc] at h
  exact h

/-- Pullback of infinity-chart functions along the local negation formula. -/
def infinityNegationLocal : Ring W true →ₐ[R] NegationNeighborhood W :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W true}) (aeval (infinityNegationCoords W))
    (by
      change Ideal.span {equation W true} ≤ RingHom.ker (aeval (infinityNegationCoords W)).toRingHom
      rw [Ideal.span_le]
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      exact infinityNegationCoords_root W)

@[simp] theorem infinityNegationLocal_coord (i : Fin 2) :
    infinityNegationLocal W (coord W true i) = infinityNegationCoords W i := by
  change aeval _ (MvPolynomial.X i) = _
  simp

/-- Negation near infinity as a morphism into the infinity chart. -/
def infinityNegationMorphism : Spec (.of (NegationNeighborhood W)) ⟶ chart W true :=
  Spec.map (CommRingCat.ofHom (infinityNegationLocal W).toRingHom)

end WeierstrassCurve.CubicCharts
