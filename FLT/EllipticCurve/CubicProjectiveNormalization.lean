/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicAffineCommutativity

/-! # Factoring normalized projective laws through their actual domains -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem chartPairSum_productMap (b c : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : Ring W b →ₐ[R] S) (g : Ring W c →ₐ[R] S) :
    Algebra.TensorProduct.productMap f g ∘ chartPairSum W b c =
      (W.map (algebraMap R S)).toProjective.addXYZ
        (chartPointCoords W b f) (chartPointCoords W c g) := by
  let k := Algebra.TensorProduct.productMap f g
  have hl : k ∘ chartPairLeft W b c = chartPointCoords W b f := by
    have h := chartPointCoords_baseChange W b k
      (Algebra.TensorProduct.includeLeft : Ring W b →ₐ[R] ChartPairRing W b c)
    rw [Algebra.TensorProduct.productMap_left] at h
    exact h.symm
  have hr : k ∘ chartPairRight W b c = chartPointCoords W c g := by
    have h := chartPointCoords_baseChange W c k
      (Algebra.TensorProduct.includeRight : Ring W c →ₐ[R] ChartPairRing W b c)
    rw [Algebra.TensorProduct.productMap_right] at h
    exact h.symm
  have h := Projective.baseChange_addXYZ (W' := W.toProjective) k
    (chartPairLeft W b c) (chartPairRight W b c)
  rw [hl, hr] at h
  exact h.symm

/-- A normalized homogeneous law factors through the appropriate principal open.
The normalization itself supplies the unit needed by the localization. -/
theorem projectiveAddition_factor_normalization (b c d : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : ChartPairRing W b c →ₐ[R] S) (g : Ring W d →ₐ[R] S) (t : S)
    (hg : ∀ i, chartPointCoords W d g i = f (chartPairSum W b c i) * t) :
    ∃ k : ProjectiveAdditionRing W b c d →ₐ[R] S,
      k.comp (projectiveAdditionRestriction W b c d) = f ∧
      k.comp (projectiveAdditionSum W b c d) = g := by
  have hu : f (projectiveAdditionDenominator W b c d) * t = 1 := by
    cases d
    · exact (hg 2).symm
    · exact (hg 1).symm
  let k : ProjectiveAdditionRing W b c d →ₐ[R] S :=
    IsLocalization.Away.liftAlgHom (projectiveAdditionDenominator W b c d) (f := f)
      (isUnit_iff_exists_inv.mpr ⟨t, hu⟩)
  have hk (x : ChartPairRing W b c) :
      k (projectiveAdditionRestriction W b c d x) = f x := by
    simp [k, projectiveAdditionRestriction]
  refine ⟨k, AlgHom.ext hk, ?_⟩
  have hu' : f (projectiveAdditionDenominator W b c d) *
      k (projectiveAdditionInv W b c d) = 1 := by
    have h := congrArg k (IsLocalization.Away.mul_invSelf
      (S := ProjectiveAdditionRing W b c d) (projectiveAdditionDenominator W b c d))
    change k (projectiveAdditionRestriction W b c d
      (projectiveAdditionDenominator W b c d) * projectiveAdditionInv W b c d) = k 1 at h
    rw [map_mul, hk, map_one] at h
    exact h
  have ht : k (projectiveAdditionInv W b c d) = t := by
    linear_combination t * hu' - k (projectiveAdditionInv W b c d) * hu
  have hc (i : Fin 3) :
      chartPointCoords W d (k.comp (projectiveAdditionSum W b c d)) i =
        chartPointCoords W d g i := by
    rw [projectiveAdditionSum_normalized_map, hk, ht]
    exact (hg i).symm
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  cases d <;> fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 0
  · exact hc 2


theorem chartPairSum_swap (b c : Bool) :
    (Algebra.TensorProduct.comm R (Ring W b) (Ring W c)) ∘ chartPairSum W b c =
      -chartPairSum W c b := by
  let k := (Algebra.TensorProduct.comm R (Ring W b) (Ring W c)).toAlgHom
  have hl : k ∘ chartPairLeft W b c = chartPairRight W c b := by
    have h := chartPointCoords_baseChange W b k
      (Algebra.TensorProduct.includeLeft : Ring W b →ₐ[R] ChartPairRing W b c)
    rw [Algebra.TensorProduct.comm_comp_includeLeft] at h
    exact h.symm
  have hr : k ∘ chartPairRight W b c = chartPairLeft W c b := by
    have h := chartPointCoords_baseChange W c k
      (Algebra.TensorProduct.includeRight : Ring W c →ₐ[R] ChartPairRing W b c)
    rw [Algebra.TensorProduct.comm_comp_includeRight] at h
    exact h.symm
  have h := Projective.baseChange_addXYZ (W' := W.toProjective) k
    (chartPairLeft W b c) (chartPairRight W b c)
  rw [hl, hr] at h
  exact h.symm.trans (projective_addXYZ_swap _ _ _)

end WeierstrassCurve.CubicCharts
