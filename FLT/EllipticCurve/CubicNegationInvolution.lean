/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNegationGlobal

/-! # Involutivity of Weierstrass negation -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem infinityNegationLocal_denominator :
    infinityNegationLocal W (infinityNegationDenominator W) =
      IsLocalization.Away.invSelf (S := NegationNeighborhood W)
        (infinityNegationDenominator W) := by
  have h := IsLocalization.Away.mul_invSelf (S := NegationNeighborhood W)
    (infinityNegationDenominator W)
  simp only [infinityNegationDenominator, map_sub, map_neg, map_one, map_mul,
    ← IsScalarTower.algebraMap_apply R (Ring W true)] at h
  simp only [infinityNegationDenominator, map_sub, map_neg, map_one, map_mul,
    AlgHom.commutes, infinityNegationLocal_coord, infinityNegationCoords]
  linear_combination h

/-- Negation preserves the refined infinity neighborhood. -/
def neighborhoodNegation : NegationNeighborhood W →ₐ[R] NegationNeighborhood W :=
  IsLocalization.Away.liftAlgHom (infinityNegationDenominator W) (f := infinityNegationLocal W)
    (by
      rw [infinityNegationLocal_denominator]
      apply isUnit_iff_exists_inv.mpr
      refine ⟨algebraMap (Ring W true) (NegationNeighborhood W) (infinityNegationDenominator W), ?_⟩
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf _)

@[simp] theorem neighborhoodNegation_algebraMap (x : Ring W true) :
    neighborhoodNegation W (algebraMap (Ring W true) (NegationNeighborhood W) x) =
      infinityNegationLocal W x := by
  simp [neighborhoodNegation, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem neighborhoodNegation_inv :
    neighborhoodNegation W
        (IsLocalization.Away.invSelf (S := NegationNeighborhood W)
          (infinityNegationDenominator W)) =
      algebraMap (Ring W true) (NegationNeighborhood W) (infinityNegationDenominator W) := by
  let d := algebraMap (Ring W true) (NegationNeighborhood W) (infinityNegationDenominator W)
  let t : NegationNeighborhood W := IsLocalization.Away.invSelf (infinityNegationDenominator W)
  have hd : d * t = 1 := IsLocalization.Away.mul_invSelf _
  have h := congrArg (neighborhoodNegation W) hd
  change neighborhoodNegation W t = d
  change neighborhoodNegation W (d * t) = neighborhoodNegation W 1 at h
  rw [map_mul, map_one] at h
  have hn : neighborhoodNegation W d = t := by
    exact (neighborhoodNegation_algebraMap W _).trans (infinityNegationLocal_denominator W)
  rw [hn] at h
  calc
    _ = (d * t) * neighborhoodNegation W t := by rw [hd, one_mul]
    _ = d := by rw [mul_assoc, h, mul_one]

theorem neighborhoodNegation_involutive :
    (neighborhoodNegation W).comp (neighborhoodNegation W) =
      AlgHom.id R (NegationNeighborhood W) := by
  apply IsLocalization.algHom_ext (L := NegationNeighborhood W)
    (Submonoid.powers (infinityNegationDenominator W))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change neighborhoodNegation W (neighborhoodNegation W
    (algebraMap (Ring W true) (NegationNeighborhood W) (coord W true i))) = _
  simp only [neighborhoodNegation_algebraMap, infinityNegationLocal_coord,
    infinityNegationCoords, map_mul, neighborhoodNegation_inv]
  change (algebraMap (Ring W true) (NegationNeighborhood W) (coord W true i) *
      IsLocalization.Away.invSelf (infinityNegationDenominator W)) *
        algebraMap (Ring W true) (NegationNeighborhood W) (infinityNegationDenominator W) =
      algebraMap (Ring W true) (NegationNeighborhood W) (coord W true i)
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf _), IsLocalization.Away.mul_invSelf, mul_one]

/-- Negation as a self-map of its infinity neighborhood. -/
def neighborhoodNegationMorphism :
    Spec (.of (NegationNeighborhood W)) ⟶ Spec (.of (NegationNeighborhood W)) :=
  Spec.map (CommRingCat.ofHom (neighborhoodNegation W).toRingHom)

@[reassoc (attr := simp)] theorem neighborhoodNegationMorphism_involutive :
    neighborhoodNegationMorphism W ≫ neighborhoodNegationMorphism W = 𝟙 _ := by
  unfold neighborhoodNegationMorphism
  rw [← Spec.map_comp, ← Spec.map_id]
  exact congrArg (fun f : NegationNeighborhood W →ₐ[R] NegationNeighborhood W ↦
    Spec.map (CommRingCat.ofHom f.toRingHom)) (neighborhoodNegation_involutive W)

@[reassoc] theorem neighborhoodNegationMorphism_inclusion :
    neighborhoodNegationMorphism W ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (NegationNeighborhood W))) =
      infinityNegationMorphism W := by
  unfold neighborhoodNegationMorphism infinityNegationMorphism
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (neighborhoodNegation_algebraMap W)

@[reassoc] theorem neighborhood_inclusion_negation :
    Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (NegationNeighborhood W))) ≫
        infinityChart W ≫ negation W =
      neighborhoodNegationMorphism W ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (NegationNeighborhood W))) ≫
          infinityChart W := by
  rw [infinityChart_negation, neighborhood_infinityNegationGlued,
    ← neighborhoodNegationMorphism_inclusion, Category.assoc]

/-- Applying the global negation twice is the identity. -/
@[reassoc (attr := simp)] theorem negation_involutive :
    negation W ≫ negation W = 𝟙 (scheme W) := by
  have ha : affineChart W ≫ negation W ≫ negation W = affineChart W := by
    rw [affineChart_negation_assoc, affineChart_negation, ← Category.assoc,
      affineNegation_involutive, Category.id_comp]
  apply pushout.hom_ext
  · change affineChart W ≫ (negation W ≫ negation W) = affineChart W ≫ 𝟙 _
    simpa only [Category.comp_id] using ha
  · change infinityChart W ≫ (negation W ≫ negation W) = infinityChart W ≫ 𝟙 _
    rw [Category.comp_id]
    apply (negationInfinityCover W).hom_ext
    intro b
    cases b
    · change overlapInclusion W true ≫ (infinityChart W ≫ negation W ≫ negation W) =
        overlapInclusion W true ≫ infinityChart W
      rw [← Category.assoc, ← changeChart_true_to_scheme, Category.assoc, ha]
    · change Spec.map (CommRingCat.ofHom
          (algebraMap (Ring W true) (NegationNeighborhood W))) ≫
          (infinityChart W ≫ negation W ≫ negation W) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (Ring W true) (NegationNeighborhood W))) ≫ infinityChart W
      rw [neighborhood_inclusion_negation_assoc, neighborhood_inclusion_negation,
        ← Category.assoc, neighborhoodNegationMorphism_involutive, Category.id_comp]

/-- Global negation is an automorphism, with itself as inverse. -/
def negationIso : scheme W ≅ scheme W where
  hom := negation W
  inv := negation W
  hom_inv_id := negation_involutive W
  inv_hom_id := negation_involutive W

instance negation_isIso : IsIso (negation W) := (negationIso W).isIso_hom

/-- Evaluation at infinity, expressed on the glued chart's quotient presentation. -/
def infinityOrigin : Ring W true →ₐ[R] R := InfinityChart.origin W

@[simp] theorem infinityOrigin_coord (i : Fin 2) :
    infinityOrigin W (coord W true i) = 0 := by
  change MvPolynomial.aeval (fun _ : Fin 2 ↦ (0 : R)) (MvPolynomial.X i) = 0
  simp

@[simp] theorem origin_negationDenominator :
    infinityOrigin W (infinityNegationDenominator W) = -1 := by
  simp only [infinityNegationDenominator, map_sub, map_neg, map_one, map_mul,
    infinityOrigin_coord, mul_zero, sub_zero]

/-- The infinity section factors through the neighborhood used to define negation. -/
def neighborhoodOrigin : NegationNeighborhood W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinityNegationDenominator W)
    (f := infinityOrigin W) (by rw [origin_negationDenominator]; exact isUnit_neg_one)

@[simp] theorem neighborhoodOrigin_algebraMap (x : Ring W true) :
    neighborhoodOrigin W (algebraMap (Ring W true) (NegationNeighborhood W) x) =
      infinityOrigin W x := by
  simp [neighborhoodOrigin, IsLocalization.Away.liftAlgHom_apply]

/-- Local negation fixes the origin of the infinity chart. -/
theorem neighborhoodOrigin_negation :
    (neighborhoodOrigin W).comp (infinityNegationLocal W) = infinityOrigin W := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change neighborhoodOrigin W (infinityNegationLocal W (coord W true i)) =
    infinityOrigin W (coord W true i)
  rw [infinityNegationLocal_coord]
  simp only [infinityNegationCoords, map_mul, neighborhoodOrigin_algebraMap,
    infinityOrigin_coord, zero_mul]

/-- The global negation fixes the infinity section. -/
@[reassoc (attr := simp)] theorem infinity_negation :
    infinity W ≫ negation W = infinity W := by
  have hfactor :
      Spec.map (CommRingCat.ofHom (neighborhoodOrigin W).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (Ring W true) (NegationNeighborhood W))) =
        InfinityChart.infinity W := by
    unfold InfinityChart.infinity
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (neighborhoodOrigin_algebraMap W)
  have hfix : Spec.map (CommRingCat.ofHom (neighborhoodOrigin W).toRingHom) ≫
      infinityNegationMorphism W = InfinityChart.infinity W := by
    unfold infinityNegationMorphism InfinityChart.infinity
    rw [← Spec.map_comp]
    exact congrArg (fun f : Ring W true →ₐ[R] R ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
      (neighborhoodOrigin_negation W)
  unfold infinity
  rw [Category.assoc, infinityChart_negation, ← hfactor, Category.assoc,
    neighborhood_infinityNegationGlued, ← Category.assoc, hfix, hfactor]

end WeierstrassCurve.CubicCharts
