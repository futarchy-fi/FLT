/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNegation
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Negation on the refined overlap -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The intersection where both infinity-chart denominators are invertible. -/
abbrev NegationOverlap := Localization.Away
  (algebraMap (Ring W true) (Overlap W true) (infinityNegationDenominator W))

/-- Restriction from the old overlap to the refined overlap. -/
def negationOverlapRestriction : Overlap W true →ₐ[R] NegationOverlap W :=
  IsScalarTower.toAlgHom R (Overlap W true) (NegationOverlap W)

/-- Restriction from the negation neighborhood to the refined overlap. -/
def negationNeighborhoodRestriction : NegationNeighborhood W →ₐ[R] NegationOverlap W :=
  IsLocalization.Away.liftAlgHom (infinityNegationDenominator W)
    (f := IsScalarTower.toAlgHom R (Ring W true) (NegationOverlap W)) (by
      change IsUnit (algebraMap (Ring W true) (NegationOverlap W)
        (infinityNegationDenominator W))
      simpa only [← IsScalarTower.algebraMap_apply (Ring W true) (Overlap W true)
        (NegationOverlap W)] using
        (IsLocalization.Away.algebraMap_isUnit (S := NegationOverlap W)
          (algebraMap (Ring W true) (Overlap W true) (infinityNegationDenominator W))))

@[simp] theorem negationNeighborhoodRestriction_algebraMap (x : Ring W true) :
    negationNeighborhoodRestriction W (algebraMap (Ring W true) (NegationNeighborhood W) x) =
      algebraMap (Ring W true) (NegationOverlap W) x :=
by
  simp [negationNeighborhoodRestriction, IsLocalization.Away.liftAlgHom_apply]

/-- The infinity-chart pullback for negation, restricted to the refined overlap. -/
def negationOverlapLocal : Ring W true →ₐ[R] NegationOverlap W :=
  (negationNeighborhoodRestriction W).comp (infinityNegationLocal W)

/-- The inverse of the negation denominator on the refined overlap. -/
def negationOverlapInv : NegationOverlap W :=
  negationNeighborhoodRestriction W (IsLocalization.Away.invSelf (infinityNegationDenominator W))

@[simp] theorem negationOverlapLocal_coord (i : Fin 2) :
    negationOverlapLocal W (coord W true i) =
      algebraMap (Ring W true) (NegationOverlap W) (coord W true i) * negationOverlapInv W := by
  simp [negationOverlapLocal, infinityNegationCoords, negationOverlapInv]

theorem negationOverlapInv_mul :
    negationOverlapInv W *
      algebraMap (Ring W true) (NegationOverlap W) (infinityNegationDenominator W) = 1 := by
  have h := congrArg (negationNeighborhoodRestriction W)
    (IsLocalization.Away.mul_invSelf (S := NegationNeighborhood W) (infinityNegationDenominator W))
  rw [map_mul, negationNeighborhoodRestriction_algebraMap, map_one] at h
  rw [mul_comm]
  exact h

/-- The negated point still belongs to the ordinary overlap. -/
theorem negationOverlapLocal_coord_one_isUnit :
    IsUnit (negationOverlapLocal W (coord W true 1)) := by
  rw [negationOverlapLocal_coord]
  apply IsUnit.mul
  · simpa only [← IsScalarTower.algebraMap_apply (Ring W true) (Overlap W true)
      (NegationOverlap W)] using
      (IsLocalization.Away.algebraMap_isUnit (S := Overlap W true) (coord W true 1)).map
        (algebraMap (Overlap W true) (NegationOverlap W))
  · exact isUnit_iff_exists_inv.mpr ⟨_, negationOverlapInv_mul W⟩

/-- Negation maps the refined overlap to the original overlap. -/
def negationOverlapMap : Overlap W true →ₐ[R] NegationOverlap W :=
  IsLocalization.Away.liftAlgHom (coord W true 1) (f := negationOverlapLocal W)
    (negationOverlapLocal_coord_one_isUnit W)

@[simp] theorem negationOverlapMap_loc (i : Fin 2) :
    negationOverlapMap W (loc W true i) =
      algebraMap (Ring W true) (NegationOverlap W) (coord W true i) * negationOverlapInv W := by
  simp [negationOverlapMap, loc, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem negationOverlapRestriction_loc (i : Fin 2) :
    negationOverlapRestriction W (loc W true i) =
      algebraMap (Ring W true) (NegationOverlap W) (coord W true i) :=
  (IsScalarTower.algebraMap_apply (Ring W true) (Overlap W true)
    (NegationOverlap W) (coord W true i)).symm

theorem negationOverlap_coord_inv :
    algebraMap (Ring W true) (NegationOverlap W) (coord W true 1) *
      negationOverlapRestriction W (inv W true) = 1 := by
  have h := congrArg (negationOverlapRestriction W) (loc_mul_inv W true)
  simpa only [map_mul, negationOverlapRestriction_loc, map_one] using h

@[simp] theorem negationOverlapMap_inv :
    negationOverlapMap W (inv W true) =
      algebraMap (Ring W true) (NegationOverlap W) (infinityNegationDenominator W) *
        negationOverlapRestriction W (inv W true) := by
  have h := congrArg (negationOverlapMap W) (loc_mul_inv W true)
  rw [map_mul, negationOverlapMap_loc, map_one] at h
  let v := algebraMap (Ring W true) (NegationOverlap W) (coord W true 1)
  let d := algebraMap (Ring W true) (NegationOverlap W) (infinityNegationDenominator W)
  let i := negationOverlapRestriction W (inv W true)
  let t := negationOverlapInv W
  have hv : v * i = 1 := negationOverlap_coord_inv W
  have hd : t * d = 1 := negationOverlapInv_mul W
  have hp : (d * i) * (v * t) = 1 := by
    calc
      _ = (v * i) * (t * d) := by ring
      _ = 1 := by rw [hv, hd, one_mul]
  change (v * t) * negationOverlapMap W (inv W true) = 1 at h
  change negationOverlapMap W (inv W true) = d * i
  calc
    _ = ((d * i) * (v * t)) * negationOverlapMap W (inv W true) := by rw [hp, one_mul]
    _ = d * i := by rw [mul_assoc, h, mul_one]

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine and infinity formulas induce the same homomorphism on the refined overlap. -/
theorem negation_overlap_compatibility :
    ((negationOverlapRestriction W).comp (changeChart W true)).comp
        (affineNegationEquiv W).toAlgHom =
      (negationOverlapMap W).comp (changeChart W true) := by
  let c : Ring W false →ₐ[R] Overlap W true := changeChart W true
  have hc0 : c (coord W false 0) = loc W true 0 * inv W true :=
    changeChart_coord W true 0
  have hc1 : c (coord W false 1) = inv W true := changeChart_coord W true 1
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change negationOverlapRestriction W (c (affineNegationEquiv W (coord W false i))) =
    negationOverlapMap W (c (coord W false i))
  fin_cases i <;> dsimp only
  · change negationOverlapRestriction W (c (affineNegationEquiv W (coord W false 0))) =
      negationOverlapMap W (c (coord W false 0))
    refine (congrArg (fun x ↦ negationOverlapRestriction W (c x))
      (affineNegationEquiv_coord_zero W)).trans ?_
    rw [hc0]
    rw [map_mul, map_mul, negationOverlapRestriction_loc,
      negationOverlapMap_loc, negationOverlapMap_inv]
    have h := negationOverlapInv_mul W
    linear_combination
      -algebraMap (Ring W true) (NegationOverlap W) (coord W true 0) *
        negationOverlapRestriction W (inv W true) * h
  · change negationOverlapRestriction W (c (affineNegationEquiv W (coord W false 1))) =
      negationOverlapMap W (c (coord W false 1))
    refine (congrArg (fun x ↦ negationOverlapRestriction W (c x))
      (affineNegationEquiv_coord_one W)).trans ?_
    simp only [map_sub, map_neg, map_mul, AlgHom.commutes, hc0, hc1,
      negationOverlapRestriction_loc, negationOverlapMap_inv]
    simp only [infinityNegationDenominator, map_sub, map_neg, map_one, map_mul,
      ← IsScalarTower.algebraMap_apply R (Ring W true)]
    have h := negationOverlap_coord_inv W
    linear_combination algebraMap R (NegationOverlap W) W.a₃ * h

/-- The infinity-to-affine coordinate change describes the same point of the glued cubic. -/
theorem changeChart_true_to_scheme :
    Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) ≫ affineChart W =
      overlapInclusion W true ≫ infinityChart W := by
  have hi : (overlapIso W).inv =
      Spec.map (CommRingCat.ofHom (transition W true).toRingHom) := rfl
  have hc : Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) =
      (overlapIso W).inv ≫ overlapInclusion W false := by
    rw [hi]
    unfold overlapInclusion
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change changeChart W true x =
      transition W true (algebraMap (Ring W false) (Overlap W false) x)
    have hu : IsUnit (changeChart W true (coord W (!true) 1)) := by
      rw [changeChart_coord]
      exact isUnit_iff_exists_inv.mpr ⟨loc W true 1, inv_mul_loc W true⟩
    exact (IsLocalization.Away.lift_eq (coord W (!true) 1) hu x).symm
  rw [hc]
  have h := congrArg (fun f ↦ (overlapIso W).inv ≫ f) (overlap_condition W)
  simpa only [overlapRight, ← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h

/-- On the refined overlap the two local negation morphisms agree as scheme morphisms. -/
theorem negation_refined_overlap_agreement :
    Spec.map (CommRingCat.ofHom
        ((negationOverlapRestriction W).comp (changeChart W true)).toRingHom) ≫
        affineNegation W ≫ affineChart W =
      Spec.map (CommRingCat.ofHom (negationNeighborhoodRestriction W).toRingHom) ≫
        infinityNegationMorphism W ≫ infinityChart W := by
  have h := congrArg (fun f : Ring W false →ₐ[R] NegationOverlap W ↦
    Spec.map (CommRingCat.ofHom f.toRingHom)) (negation_overlap_compatibility W)
  have hl :
      Spec.map (CommRingCat.ofHom
          ((negationOverlapRestriction W).comp (changeChart W true)).toRingHom) ≫
          affineNegation W =
        Spec.map (CommRingCat.ofHom (negationOverlapMap W).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (changeChart W true).toRingHom) := by
    unfold affineNegation
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact h
  rw [← Category.assoc, hl, Category.assoc, changeChart_true_to_scheme]
  unfold infinityNegationMorphism overlapInclusion
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change negationOverlapMap W (algebraMap (Ring W true) (Overlap W true) x) =
    negationNeighborhoodRestriction W (infinityNegationLocal W x)
  simp [negationOverlapMap, IsLocalization.Away.liftAlgHom_apply, negationOverlapLocal]

/-- The refined overlap is the scheme-theoretic intersection of the two infinity opens. -/
theorem negation_refined_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (negationOverlapRestriction W).toRingHom))
      (Spec.map (CommRingCat.ofHom (negationNeighborhoodRestriction W).toRingHom))
      (overlapInclusion W true)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Ring W true) (NegationNeighborhood W)))) := by
  let : Algebra (NegationNeighborhood W) (NegationOverlap W) :=
    (negationNeighborhoodRestriction W).toRingHom.toAlgebra
  let : IsScalarTower (Ring W true) (NegationNeighborhood W) (NegationOverlap W) :=
    IsScalarTower.of_algebraMap_eq
      (R := Ring W true) (S := NegationNeighborhood W) (A := NegationOverlap W)
      (fun x ↦ (negationNeighborhoodRestriction_algebraMap W x).symm)
  have : IsLocalization
      (Algebra.algebraMapSubmonoid (Overlap W true)
        (Submonoid.powers (infinityNegationDenominator W))) (NegationOverlap W) := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstance : IsLocalization
        (Submonoid.powers (algebraMap (Ring W true) (Overlap W true)
          (infinityNegationDenominator W))) (NegationOverlap W))
  have : Algebra.IsPushout (Ring W true) (Overlap W true) (NegationNeighborhood W)
      (NegationOverlap W) :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers (infinityNegationDenominator W))
      (NegationNeighborhood W) (Overlap W true) (NegationOverlap W)
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (Ring W true) (Overlap W true)
      (NegationNeighborhood W) (NegationOverlap W))

end WeierstrassCurve.CubicCharts
