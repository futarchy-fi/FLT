/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityFiniteComparison
public import FLT.EllipticCurve.CubicMixedProjective

/-! # Projective comparison after changing a finite infinity-chart input -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem changeChart_projective_scaled :
    chartPointCoords W true (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) =
      loc W true 1 • chartPointCoords W false (changeChart W true) := by
  ext i
  fin_cases i
  · change loc W true 0 = loc W true 1 * changeChart W true (coord W (!true) 0)
    rw [changeChart_coord]
    change loc W true 0 = loc W true 1 * (loc W true 0 * inv W true)
    rw [← mul_assoc, mul_comm (loc W true 1), mul_assoc, loc_mul_inv, mul_one]
  · change 1 = loc W true 1 * changeChart W true (coord W (!true) 1)
    rw [changeChart_coord]
    exact (loc_mul_inv W true).symm
  · change loc W true 1 = loc W true 1 * 1
    rw [mul_one]

theorem changeChart_projective_scaled_map
    {S : Type u} [CommRing S] [Algebra R S] (f : Overlap W true →ₐ[R] S) :
    chartPointCoords W true
        (f.comp (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true))) =
      f (loc W true 1) • chartPointCoords W false (f.comp (changeChart W true)) := by
  ext i
  rw [chartPointCoords_baseChange, chartPointCoords_baseChange]
  change f (chartPointCoords W true
    (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) i) =
      f (loc W true 1) * f (chartPointCoords W false (changeChart W true) i)
  rw [changeChart_projective_scaled]
  exact f.map_mul _ _

theorem infinityFiniteAffine_projective (b : Bool) :
    chartPointCoords W true (infinityFiniteInput W b b) =
      infinityFiniteInput W b b (coord W true 1) •
        chartPointCoords W false (infinityFiniteAffine W b) := by
  have ha : (infinityFiniteOverlap W b).comp
      (IsScalarTower.toAlgHom R (Ring W true) (Overlap W true)) =
        infinityFiniteInput W b b := AlgHom.ext (infinityFiniteOverlap_restriction W b)
  have h := changeChart_projective_scaled_map W (infinityFiniteOverlap W b)
  rw [ha] at h
  have hv : infinityFiniteOverlap W b (loc W true 1) =
      infinityFiniteInput W b b (coord W true 1) :=
    infinityFiniteOverlap_restriction W b (coord W true 1)
  rw [hv] at h
  exact h

theorem infinityFinite_projective_inputs (b : Bool) :
    infinityFiniteRestriction W b ∘ chartPairLeft W true true =
        chartPointCoords W true (infinityFiniteInput W b false) ∧
      infinityFiniteRestriction W b ∘ chartPairRight W true true =
        chartPointCoords W true (infinityFiniteInput W b true) := by
  constructor
  · exact (chartPointCoords_baseChange W true (infinityFiniteRestriction W b)
      (infinityPairInput W false)).symm
  · exact (chartPointCoords_baseChange W true (infinityFiniteRestriction W b)
      (infinityPairInput W true)).symm

/-- Changing one finite input rescales the homogeneous sum by an invertible square. -/
theorem infinityFinite_projective_sum (b : Bool) :
    infinityFiniteRestriction W b ∘ chartPairSum W true true =
      infinityFiniteInput W b b (coord W true 1) ^ 2 •
        (infinityFinitePair W b ∘ chartPairSum W b (!b)) := by
  have h := Projective.baseChange_addXYZ (W' := W.toProjective) (infinityFiniteRestriction W b)
    (chartPairLeft W true true) (chartPairRight W true true)
  rw [(infinityFinite_projective_inputs W b).1,
    (infinityFinite_projective_inputs W b).2] at h
  cases b
  · rw [infinityFiniteAffine_projective W false] at h
    have hs := Projective.addXYZ_smul
      (W' := (W.map (algebraMap R (InfinityFiniteRing W false))).toProjective)
      (chartPointCoords W false (infinityFiniteAffine W false))
      (chartPointCoords W true (infinityFiniteInput W false true))
      (infinityFiniteInput W false false (coord W true 1)) 1
    simp only [one_smul, mul_one] at hs
    have hm := chartPairSum_productMap W false true
      (infinityFiniteAffine W false) (infinityFiniteInput W false true)
    exact h.symm.trans (hs.trans (congrArg
      (infinityFiniteInput W false false (coord W true 1) ^ 2 • ·) hm.symm))
  · rw [infinityFiniteAffine_projective W true] at h
    have hs := Projective.addXYZ_smul
      (W' := (W.map (algebraMap R (InfinityFiniteRing W true))).toProjective)
      (chartPointCoords W true (infinityFiniteInput W true false))
      (chartPointCoords W false (infinityFiniteAffine W true))
      1 (infinityFiniteInput W true true (coord W true 1))
    simp only [one_smul, one_mul] at hs
    have hm := chartPairSum_productMap W true false
      (infinityFiniteInput W true false) (infinityFiniteAffine W true)
    exact h.symm.trans (hs.trans (congrArg
      (infinityFiniteInput W true true (coord W true 1) ^ 2 • ·) hm.symm))

/-- A normalized projective output on a finite-input piece is its descended addition. -/
theorem infinityFiniteAddition_normalized [W.IsElliptic] (b d : Bool)
    {S : Type u} [CommRing S] [Algebra R S]
    (f : InfinityFiniteRing W b →ₐ[R] S) (g : Ring W d →ₐ[R] S) (t : S)
    (hg : ∀ i, chartPointCoords W d g i =
      f (infinityFiniteRestriction W b (chartPairSum W true true i)) * t) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityFiniteAddition W b =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ sourceChart W d := by
  have hn (i : Fin 3) : chartPointCoords W d g i =
      (f.comp (infinityFinitePair W b)) (chartPairSum W b (!b) i) *
        (f (infinityFiniteInput W b b (coord W true 1)) ^ 2 * t) := by
    have h := congrArg f (congrFun (infinityFinite_projective_sum W b) i)
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at h
    rw [hg, h]
    simp only [AlgHom.comp_apply]
    ring
  cases b
  · change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (infinityFinitePair W false).toRingHom) ≫
        oppositeMixedAddition W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    exact oppositeMixedAddition_normalized W d (f.comp (infinityFinitePair W false)) g _ hn
  · change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (infinityFinitePair W true).toRingHom) ≫
        mixedChartAddition W) = _
    rw [← Category.assoc, ← Spec.map_comp]
    exact mixedChartAddition_normalized W d (f.comp (infinityFinitePair W true)) g _ hn

end WeierstrassCurve.CubicCharts
