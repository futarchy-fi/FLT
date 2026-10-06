/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicMixedChartAddition

/-! # The opposite mixed chart and the two infinity identities -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Swap the infinity and ordinary affine factors. -/
def mixedPairSwap : ChartPairRing W true false ≃ₐ[R] ChartPairRing W false true :=
  Algebra.TensorProduct.comm R (Ring W true) (Ring W false)

/-- Addition on the whole ordinary-affine-chart times infinity-chart product. -/
def oppositeMixedAddition [W.IsElliptic] :
    Spec (.of (ChartPairRing W false true)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (mixedPairSwap W).toRingHom) ≫ mixedChartAddition W

@[reassoc (attr := simp)] theorem oppositeMixedAddition_toBase [W.IsElliptic] :
    oppositeMixedAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartPairRing W false true))) := by
  unfold oppositeMixedAddition
  rw [Category.assoc, mixedChartAddition_toBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (mixedPairSwap W).toAlgHom.comp_algebraMap

/-- The opposite mixed addition on the categorical product of input charts. -/
def oppositeMixedAdditionMorphism [W.IsElliptic] :
    pullback (chartToBase W false) (chartToBase W true) ⟶ scheme W :=
  (pullbackSpecIso R (Ring W false) (Ring W true)).hom ≫ oppositeMixedAddition W

@[reassoc] theorem mixedChartAddition_zero [W.IsElliptic] :
    Spec.map (CommRingCat.ofHom (zeroAffineEvaluation W).toRingHom) ≫ mixedChartAddition W =
      affineChart W := by
  have hi : zeroAffineSection W ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ChartPairRing W true false)
        (ProjectiveAdditionRing W true false false))) =
      Spec.map (CommRingCat.ofHom (zeroAffineEvaluation W).toRingHom) := by
    unfold zeroAffineSection
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (zeroAffinePoint_restriction W)
  rw [← hi, Category.assoc]
  exact mixedChartAddition_infinity W

/-- Evaluate the second input at infinity and retain the first affine input. -/
def affineZeroEvaluation : ChartPairRing W false true →ₐ[R] Ring W false :=
  Algebra.TensorProduct.productMap (AlgHom.id R _)
    ((Algebra.ofId R (Ring W false)).comp (InfinityChart.origin W))

theorem mixedPairSwap_zero :
    (affineZeroEvaluation W).comp (mixedPairSwap W).toAlgHom = zeroAffineEvaluation W := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change y * algebraMap R (Ring W false) (InfinityChart.origin W x) =
    algebraMap R (Ring W false) (InfinityChart.origin W x) * y
  exact mul_comm _ _

/-- The opposite mixed addition has the expected right identity on the full affine chart. -/
@[reassoc] theorem oppositeMixedAddition_zero [W.IsElliptic] :
    Spec.map (CommRingCat.ofHom (affineZeroEvaluation W).toRingHom) ≫ oppositeMixedAddition W =
      affineChart W := by
  unfold oppositeMixedAddition
  rw [← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (mixedPairSwap W).toRingHom ≫
      CommRingCat.ofHom (affineZeroEvaluation W).toRingHom =
      CommRingCat.ofHom (zeroAffineEvaluation W).toRingHom := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (mixedPairSwap_zero W)
  rw [h, mixedChartAddition_zero]

end WeierstrassCurve.CubicCharts
