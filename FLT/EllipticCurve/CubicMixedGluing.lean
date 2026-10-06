/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicMixedAffine
public import FLT.EllipticCurve.CubicVerticalProjective

/-! # Compatibility on the mixed-chart addition cover -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem mixedAffine_left_scaled :
    mixedAffineRestriction W ∘ chartPairLeft W true false =
      mixedAffineLeft W (coord W true 1) • chartPointCoords W false (mixedAffineFirst W) := by
  have hu : mixedAffineLeft W (coord W true 1) *
      IsLocalization.Away.invSelf (mixedFirstZ W) = 1 :=
    IsLocalization.Away.mul_invSelf (S := MixedAffineRing W) (mixedFirstZ W)
  ext i
  fin_cases i
  · change mixedAffineLeft W (coord W true 0) =
      mixedAffineLeft W (coord W true 1) * mixedAffineFirst W (coord W false 0)
    rw [mixedAffineFirst_coord_zero]
    linear_combination -mixedAffineLeft W (coord W true 0) * hu
  · change mixedAffineRestriction W 1 =
      mixedAffineLeft W (coord W true 1) * mixedAffineFirst W (coord W false 1)
    rw [mixedAffineFirst_coord_one]
    exact (mixedAffineRestriction W).map_one.trans hu.symm
  · change mixedAffineLeft W (coord W true 1) = mixedAffineLeft W (coord W true 1) * 1
    rw [mul_one]

theorem mixedAffine_right_projective :
    mixedAffineRestriction W ∘ chartPairRight W true false =
      chartPointCoords W false (mixedAffineRight W) := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact (mixedAffineRestriction W).map_one

theorem mixedAffine_projective_sum :
    mixedAffineRestriction W ∘ chartPairSum W true false =
      mixedAffineLeft W (coord W true 1) ^ 2 •
        (W.map (algebraMap R (MixedAffineRing W))).toProjective.addXYZ
          (chartPointCoords W false (mixedAffineFirst W))
          (chartPointCoords W false (mixedAffineRight W)) := by
  have h := Projective.baseChange_addXYZ (W' := W.toProjective) (mixedAffineRestriction W)
    (chartPairLeft W true false) (chartPairRight W true false)
  rw [mixedAffine_left_scaled, mixedAffine_right_projective] at h
  have hs := Projective.addXYZ_smul
    (W' := (W.map (algebraMap R (MixedAffineRing W))).toProjective)
    (chartPointCoords W false (mixedAffineFirst W))
    (chartPointCoords W false (mixedAffineRight W)) (mixedAffineLeft W (coord W true 1)) 1
  simp only [one_smul, mul_one] at hs
  exact h.symm.trans hs

/-- Compatibility for arbitrary common coefficient algebras, hence for the
scheme-theoretic intersection of the two mixed-chart opens. -/
theorem mixed_addition_agreement [W.IsElliptic] {d : Bool}
    {S : Type u} [CommRing S] [Algebra R S]
    (f : MixedAffineRing W →ₐ[R] S)
    (g : ProjectiveAdditionRing W true false d →ₐ[R] S)
    (h : f.comp (mixedAffineRestriction W) =
      g.comp (projectiveAdditionRestriction W true false d)) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ mixedAffineAddition W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveAddition W true false d := by
  let a := f.comp (mixedAffineFirst W)
  let b := f.comp (mixedAffineRight W)
  let E := W.map (algebraMap R S)
  let P := E.toProjective.addXYZ (chartPointCoords W false a) (chartPointCoords W false b)
  have hp (i : Fin 3) :
      g (projectiveAdditionRestriction W true false d (chartPairSum W true false i)) =
        f (mixedAffineLeft W (coord W true 1)) ^ 2 * P i := by
    have he := DFunLike.congr_fun h (chartPairSum W true false i)
    change f (mixedAffineRestriction W (chartPairSum W true false i)) =
      g (projectiveAdditionRestriction W true false d (chartPairSum W true false i)) at he
    have hm := congrArg f (congrFun (mixedAffine_projective_sum W) i)
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hm
    have hb := Projective.baseChange_addXYZ (W' := W.toProjective) f
      (chartPointCoords W false (mixedAffineFirst W))
      (chartPointCoords W false (mixedAffineRight W))
    rw [← chartPointCoords_baseChange, ← chartPointCoords_baseChange] at hb
    exact he.symm.trans (hm.trans
      (congrArg (fun x ↦ f (mixedAffineLeft W (coord W true 1)) ^ 2 * x) (congrFun hb i).symm))
  have hg (i : Fin 3) :
      chartPointCoords W d (g.comp (projectiveAdditionSum W true false d)) i =
        P i * (f (mixedAffineLeft W (coord W true 1)) ^ 2 *
          g (projectiveAdditionInv W true false d)) := by
    rw [projectiveAdditionSum_normalized_map, hp]
    ring
  have he : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap a b).toRingHom) ≫
      affineAddition W =
        Spec.map (CommRingCat.ofHom (g.comp (projectiveAdditionSum W true false d)).toRingHom) ≫
          sourceChart W d := by
    cases d
    · exact affineAddition_projective_comparison W a b
        (g.comp (projectiveAdditionSum W true false false))
        (f (mixedAffineLeft W (coord W true 1)) ^ 2 *
          g (projectiveAdditionInv W true false false)) hg
    · exact affineAddition_projective_infinity_comparison W a b
        (g.comp (projectiveAdditionSum W true false true))
        (f (mixedAffineLeft W (coord W true 1)) ^ 2 *
          g (projectiveAdditionInv W true false true)) hg
  have hi : f.comp (mixedAffineInputs W) = Algebra.TensorProduct.productMap a b := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact f.map_mul (mixedAffineFirst W x) (mixedAffineRight W y)
  unfold mixedAffineAddition projectiveAddition
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (f.comp (mixedAffineInputs W)).toRingHom) ≫
    affineAddition W = _
  rw [hi]
  exact he

end WeierstrassCurve.CubicCharts
