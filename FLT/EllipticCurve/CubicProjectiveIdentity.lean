/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicProjectiveLocal

/-! # The infinity section on a projective addition domain -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluate the first input at infinity and retain the second affine input. -/
def zeroAffineEvaluation : ChartPairRing W true false →ₐ[R] Ring W false :=
  Algebra.TensorProduct.productMap
    ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)) (AlgHom.id R _)

theorem infinity_origin_coord (i : Fin 2) :
    InfinityChart.origin W (coord W true i) = 0 := by
  change aeval (fun _ : Fin 2 ↦ (0 : R)) (X i) = 0
  simp

theorem zeroAffineEvaluation_left :
    zeroAffineEvaluation W ∘ chartPairLeft W true false = ![0, 1, 0] := by
  ext i
  fin_cases i
  · change zeroAffineEvaluation W (Algebra.TensorProduct.includeLeft (coord W true 0)) = 0
    simp only [zeroAffineEvaluation, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      map_one, mul_one]
    exact (congrArg (Algebra.ofId R (Ring W false)) (infinity_origin_coord W 0)).trans (map_zero _)
  · exact (zeroAffineEvaluation W).map_one
  · change zeroAffineEvaluation W (Algebra.TensorProduct.includeLeft (coord W true 1)) = 0
    simp only [zeroAffineEvaluation, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      map_one, mul_one]
    exact (congrArg (Algebra.ofId R (Ring W false)) (infinity_origin_coord W 1)).trans (map_zero _)

theorem zeroAffineEvaluation_right :
    zeroAffineEvaluation W ∘ chartPairRight W true false =
      ![coord W false 0, coord W false 1, 1] := by
  ext i
  fin_cases i
  · change zeroAffineEvaluation W (Algebra.TensorProduct.includeRight (coord W false 0)) =
      coord W false 0
    exact DFunLike.congr_fun (Algebra.TensorProduct.productMap_right
      ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W))
      (AlgHom.id R (Ring W false))) _
  · change zeroAffineEvaluation W (Algebra.TensorProduct.includeRight (coord W false 1)) =
      coord W false 1
    exact DFunLike.congr_fun (Algebra.TensorProduct.productMap_right
      ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W))
      (AlgHom.id R (Ring W false))) _
  · exact (zeroAffineEvaluation W).map_one

theorem zeroAffineEvaluation_sum :
    zeroAffineEvaluation W ∘ chartPairSum W true false =
      ![coord W false 0, coord W false 1, 1] := by
  have h := Projective.baseChange_addXYZ (W' := W.toProjective)
    (zeroAffineEvaluation W) (chartPairLeft W true false) (chartPairRight W true false)
  rw [zeroAffineEvaluation_left, zeroAffineEvaluation_right] at h
  exact h.symm.trans (projective_addXYZ_zero_left _ _ _)

@[simp] theorem zeroAffineEvaluation_denominator :
    zeroAffineEvaluation W (projectiveAdditionDenominator W true false false) = 1 :=
  congrFun (zeroAffineEvaluation_sum W) 2

/-- The entire infinity-times-affine section factors through the local addition domain. -/
def zeroAffinePoint :
    ProjectiveAdditionRing W true false false →ₐ[R] Ring W false :=
  IsLocalization.Away.liftAlgHom (projectiveAdditionDenominator W true false false)
    (f := zeroAffineEvaluation W) (by rw [zeroAffineEvaluation_denominator]; exact isUnit_one)

theorem zeroAffinePoint_restriction (x : ChartPairRing W true false) :
    zeroAffinePoint W (projectiveAdditionRestriction W true false false x) =
      zeroAffineEvaluation W x := by
  simp [zeroAffinePoint, projectiveAdditionRestriction, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem zeroAffinePoint_inv :
    zeroAffinePoint W (projectiveAdditionInv W true false false) = 1 := by
  have h := congrArg (zeroAffinePoint W)
    (IsLocalization.Away.mul_invSelf
      (S := ProjectiveAdditionRing W true false false)
      (projectiveAdditionDenominator W true false false))
  rw [map_mul, map_one] at h
  change zeroAffinePoint W (projectiveAdditionRestriction W true false false
    (projectiveAdditionDenominator W true false false)) * _ = 1 at h
  simp only [zeroAffinePoint_restriction, zeroAffineEvaluation_denominator, one_mul] at h
  exact h

theorem zeroAffinePoint_sum :
    (zeroAffinePoint W).comp (projectiveAdditionSum W true false false) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change zeroAffinePoint W (projectiveAdditionSum W true false false (coord W false i)) =
    coord W false i
  rw [projectiveAdditionSum_coord]
  fin_cases i
  · change zeroAffinePoint W (projectiveAdditionRestriction W true false false
        (chartPairSum W true false 0) * projectiveAdditionInv W true false false) = _
    rw [map_mul, zeroAffinePoint_restriction, zeroAffinePoint_inv, mul_one]
    exact congrFun (zeroAffineEvaluation_sum W) 0
  · change zeroAffinePoint W (projectiveAdditionRestriction W true false false
        (chartPairSum W true false 1) * projectiveAdditionInv W true false false) = _
    rw [map_mul, zeroAffinePoint_restriction, zeroAffinePoint_inv, mul_one]
    exact congrFun (zeroAffineEvaluation_sum W) 1

/-- The section of the local domain represented by infinity and the universal affine point. -/
def zeroAffineSection : chart W false ⟶ Spec (.of (ProjectiveAdditionRing W true false false)) :=
  Spec.map (CommRingCat.ofHom (zeroAffinePoint W).toRingHom)

@[reassoc (attr := simp)] theorem zeroAffineSection_addition :
    zeroAffineSection W ≫ projectiveAddition W true false false = affineChart W := by
  unfold zeroAffineSection projectiveAddition
  rw [← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (projectiveAdditionSum W true false false).toRingHom ≫
      CommRingCat.ofHom (zeroAffinePoint W).toRingHom = 𝟙 (CommRingCat.of (Ring W false)) := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (zeroAffinePoint_sum W)
  rw [h, Spec.map_id, Category.id_comp]
  rfl

theorem zeroAffinePoint_left :
    ((zeroAffinePoint W).comp (projectiveAdditionRestriction W true false false)).comp
      (Algebra.TensorProduct.includeLeft : Ring W true →ₐ[R] ChartPairRing W true false) =
        (Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W) := by
  apply AlgHom.ext
  intro x
  change zeroAffinePoint W (projectiveAdditionRestriction W true false false
    ((Algebra.TensorProduct.includeLeft :
      Ring W true →ₐ[R] ChartPairRing W true false) x)) = _
  rw [zeroAffinePoint_restriction]
  exact DFunLike.congr_fun (Algebra.TensorProduct.productMap_left
    ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)) (AlgHom.id R _)) x

theorem zeroAffinePoint_right :
    ((zeroAffinePoint W).comp (projectiveAdditionRestriction W true false false)).comp
      (Algebra.TensorProduct.includeRight : Ring W false →ₐ[R] ChartPairRing W true false) =
        AlgHom.id R (Ring W false) := by
  apply AlgHom.ext
  intro x
  change zeroAffinePoint W (projectiveAdditionRestriction W true false false
    ((Algebra.TensorProduct.includeRight :
      Ring W false →ₐ[R] ChartPairRing W true false) x)) = _
  rw [zeroAffinePoint_restriction]
  exact DFunLike.congr_fun (Algebra.TensorProduct.productMap_right
    ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W)) (AlgHom.id R _)) x

@[reassoc] theorem zeroAffineSection_inclusion_fst :
    zeroAffineSection W ≫ projectiveAdditionInclusion W true false false ≫
      pullback.fst (toBase W) (toBase W) = chartToBase W false ≫ infinity W := by
  rw [projectiveAdditionInclusion_fst]
  unfold zeroAffineSection chartToBase infinity InfinityChart.infinity
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  change Spec.map _ ≫ infinityChart W = Spec.map _ ≫ infinityChart W
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (zeroAffinePoint_left W)

@[reassoc] theorem zeroAffineSection_inclusion_snd :
    zeroAffineSection W ≫ projectiveAdditionInclusion W true false false ≫
      pullback.snd (toBase W) (toBase W) = affineChart W := by
  rw [projectiveAdditionInclusion_snd]
  unfold zeroAffineSection
  rw [← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom
      ((projectiveAdditionRestriction W true false false).comp
        Algebra.TensorProduct.includeRight).toRingHom ≫
      CommRingCat.ofHom (zeroAffinePoint W).toRingHom = 𝟙 (CommRingCat.of (Ring W false)) := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (zeroAffinePoint_right W)
  rw [h, Spec.map_id, Category.id_comp]
  rfl

end WeierstrassCurve.CubicCharts
