/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAffineInverseCover

/-! # The inverse law for the descended affine-input addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Factorization of each inverse-graph open through a vertical addition domain. -/
def inverseVerticalMap (b : Bool) : VerticalRing W b →ₐ[R] InverseAdditionRing W b :=
  IsLocalization.Away.liftAlgHom (pairChordY W b)
    (f := (inverseAdditionRestriction W b).comp (inversePair W))
    (isUnit_iff_exists_inv.mpr ⟨IsLocalization.Away.invSelf (inverseAdditionDenominator W b),
      IsLocalization.Away.mul_invSelf
        (S := InverseAdditionRing W b) (inverseAdditionDenominator W b)⟩)

theorem inverseVerticalMap_restriction (b : Bool) (x : AffinePairRing W) :
    inverseVerticalMap W b (verticalRestriction W b x) =
      inverseAdditionRestriction W b (inversePair W x) := by
  simp [inverseVerticalMap, verticalRestriction, IsLocalization.Away.liftAlgHom_apply]

theorem inversePair_chordT_cube (b : Bool) :
    inversePair W (pairChordT W b ^ 3) = 0 := by
  have h := map_pow (inversePair W) (pairChordT W b) 3
  simp only [inversePair_chordT, zero_pow (by decide : 3 ≠ 0)] at h
  exact h

theorem inverseVerticalMap_sum (b : Bool) :
    (inverseVerticalMap W b).comp (verticalSum W b) =
      (Algebra.ofId R (InverseAdditionRing W b)).comp (InfinityChart.origin W) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change inverseVerticalMap W b (verticalSum W b (coord W true i)) =
    (Algebra.ofId R (InverseAdditionRing W b)) (InfinityChart.origin W (coord W true i))
  have ho : (Algebra.ofId R (InverseAdditionRing W b))
      (InfinityChart.origin W (coord W true i)) = 0 :=
    (congrArg (Algebra.ofId R (InverseAdditionRing W b)) (infinity_origin_coord W i)).trans
      (map_zero _)
  rw [ho, verticalSum_coord]
  fin_cases i
  · change inverseVerticalMap W b (verticalRestriction W b (pairChordX W b) * verticalInv W b) = 0
    rw [map_mul, inverseVerticalMap_restriction, inversePair_chordX, map_zero, zero_mul]
  · change inverseVerticalMap W b
      (verticalRestriction W b (pairChordT W b ^ 3) * verticalInv W b) = 0
    rw [map_mul, inverseVerticalMap_restriction, inversePair_chordT_cube, map_zero, zero_mul]

@[reassoc] theorem inverseVerticalMap_addition (b : Bool) :
    Spec.map (CommRingCat.ofHom (inverseVerticalMap W b).toRingHom) ≫ verticalAddition W b =
      Spec.map (CommRingCat.ofHom (algebraMap R (InverseAdditionRing W b))) ≫ infinity W := by
  unfold verticalAddition infinity InfinityChart.infinity
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (inverseVerticalMap_sum W b)

theorem inverseVerticalMap_square (b : Bool) :
    inverseAdditionInclusion W b ≫ Spec.map (CommRingCat.ofHom (inversePair W).toRingHom) =
      Spec.map (CommRingCat.ofHom (inverseVerticalMap W b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W b))) := by
  unfold inverseAdditionInclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (inverseVerticalMap_restriction W b x).symm

theorem inverseAddition_restrict [W.IsElliptic] (b : Bool) :
    inverseAdditionInclusion W b ≫
        Spec.map (CommRingCat.ofHom (inversePair W).toRingHom) ≫ affineAddition W =
      inverseAdditionInclusion W b ≫ chartToBase W false ≫ infinity W := by
  have hv : Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (VerticalRing W b))) ≫
      affineAddition W = verticalAddition W b := by
    cases b
    · exact affineAddition_restrict W 2
    · exact affineAddition_restrict W 3
  rw [← Category.assoc, inverseVerticalMap_square, Category.assoc, hv,
    inverseVerticalMap_addition]
  unfold inverseAdditionInclusion chartToBase
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1

/-- Every ordinary affine point sums with its scheme-theoretic negative to infinity.
The covering proof includes vertical tangents and rational two-torsion. -/
@[reassoc] theorem affineAddition_inverse [W.IsElliptic] :
    Spec.map (CommRingCat.ofHom (inversePair W).toRingHom) ≫ affineAddition W =
      chartToBase W false ≫ infinity W := by
  apply (inverseAdditionCover W).hom_ext
  intro b
  change inverseAdditionInclusion W b ≫
    (Spec.map (CommRingCat.ofHom (inversePair W).toRingHom) ≫ affineAddition W) =
      inverseAdditionInclusion W b ≫ (chartToBase W false ≫ infinity W)
  exact inverseAddition_restrict W b

end WeierstrassCurve.CubicCharts
