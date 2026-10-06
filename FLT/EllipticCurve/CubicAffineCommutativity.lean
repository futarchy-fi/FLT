/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicDenseComparison

/-! # Commutativity of the descended affine-input addition -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem projective_addXYZ_swap (P Q : Fin 3 → R) :
    W.toProjective.addXYZ P Q = -W.toProjective.addXYZ Q P := by
  rw [projective_addXYZ_polar, projective_addXYZ_polar]
  ext i
  fin_cases i <;> dsimp [Projective.neg, Projective.negY] <;> ring

/-- Interchange the two ordinary affine input factors. -/
def affinePairSwap : AffinePairRing W ≃ₐ[R] AffinePairRing W :=
  Algebra.TensorProduct.comm R (Ring W false) (Ring W false)

theorem affineAddition_swap_on_secant [W.IsElliptic] :
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.productMap (secantInput W true) (secantInput W false)).toRingHom) ≫
        affineAddition W = secantAddition W := by
  apply affineAddition_projective_comparison W (secantInput W true) (secantInput W false)
    (secantSum W) (secantInv W ^ 3)
  intro i
  let E := W.map (algebraMap R (SecantRing W))
  have hn := secantSum_normalized W i
  have hs := congrFun (projective_addXYZ_swap E
    (chartPointCoords W false (secantInput W false))
    (chartPointCoords W false (secantInput W true))) i
  change E.toProjective.addXYZ
      (chartPointCoords W false (secantInput W false))
      (chartPointCoords W false (secantInput W true)) i =
    -E.toProjective.addXYZ
      (chartPointCoords W false (secantInput W true))
      (chartPointCoords W false (secantInput W false)) i at hs
  change chartPointCoords W false (secantSum W) i =
    E.toProjective.addXYZ
      (chartPointCoords W false (secantInput W false))
      (chartPointCoords W false (secantInput W true)) i * (-secantInv W ^ 3) at hn
  rw [hs, neg_mul_neg] at hn
  exact hn

theorem affinePairSwap_secantRestriction :
    (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)).comp
        (affinePairSwap W).toAlgHom =
      Algebra.TensorProduct.productMap (secantInput W true) (secantInput W false) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change (algebraMap (AffinePairRing W) (SecantRing W)) (y ⊗ₜ[R] x) =
    secantInput W true x * secantInput W false y
  have h : y ⊗ₜ[R] x =
      (Algebra.TensorProduct.includeRight : Ring W false →ₐ[R] AffinePairRing W) x *
        (Algebra.TensorProduct.includeLeft : Ring W false →ₐ[R] AffinePairRing W) y := by
    simp
  rw [h, map_mul]
  rfl

/-- Commutativity on the whole ordinary input product, including diagonal and
vertical pairs, obtained by schematic density of the secant open. -/
theorem affineAddition_comm [W.IsElliptic] :
    Spec.map (CommRingCat.ofHom (affinePairSwap W).toRingHom) ≫ affineAddition W =
      affineAddition W := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W)))
  have : IsSchemeTheoreticallyDominant j := secant_schematic_dominance W
  refine hom_ext_of_schematic_dominance (toBase W) ?_ j ?_
  · rw [Category.assoc, affineAddition_toBase, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (affinePairSwap W).toAlgHom.comp_algebraMap
  · have hj : j ≫ affineAddition W = secantAddition W := affineAddition_restrict W 0
    rw [hj, ← Category.assoc, ← Spec.map_comp]
    have he : CommRingCat.ofHom (affinePairSwap W).toRingHom ≫
        CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W)) =
      CommRingCat.ofHom
        (Algebra.TensorProduct.productMap
          (secantInput W true) (secantInput W false)).toRingHom := by
      apply CommRingCat.hom_ext
      exact congrArg AlgHom.toRingHom (affinePairSwap_secantRestriction W)
    rw [he]
    exact affineAddition_swap_on_secant W

end WeierstrassCurve.CubicCharts
