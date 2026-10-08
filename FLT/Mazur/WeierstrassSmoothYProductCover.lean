/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothInfinityDomain
public import FLT.Mazur.WeierstrassSmoothMixedCover
public import FLT.Mazur.WeierstrassYProductCover

/-!
# A complete cover of the smooth Y/Y input product

The original affine, polynomial, and infinity domains restrict to cover every
pair of smooth Y-chart inputs, including bad reduction fibers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The three original Y/Y domains restricted to their actual smooth inputs. -/
def smoothYDomain : YProductCoverIndex → Scheme.{u}
  | .affine => (smoothAffineOverlapOpen W true true).toScheme
  | .polynomial => (polynomialSmoothInputOpen W 1 1 2).toScheme
  | .infinity => (infinitySmoothInputOpen W).toScheme

/-- The inclusions of the three restricted domains into the smooth Y/Y product. -/
def smoothYInclusion (i : YProductCoverIndex) :
    smoothYDomain W i ⟶ (smoothProductChartOpen W true true).toScheme :=
  match i with
  | .affine => smoothAffineOverlapToChart W true true
  | .polynomial => smoothPolynomialToInputs W true true 2
  | .infinity => smoothInfinityToInputs W

/-- All three inclusions are open immersions. -/
instance smoothYInclusion_isOpenImmersion (i : YProductCoverIndex) :
    IsOpenImmersion (smoothYInclusion W i) := by
  cases i <;> dsimp [smoothYInclusion] <;> infer_instance

/-- Every smooth Y/Y pair lies in an original domain with smooth inputs. -/
theorem smoothYInclusion_covers (p : (smoothProductChartOpen W true true).toScheme) :
    ∃ i, p ∈ Set.range (smoothYInclusion W i) := by
  obtain ⟨i, q, hq⟩ := yProductCoverInclusion_covers W p.val
  cases i with
  | affine =>
    have hq' : integralProductOverlapFst W true true false false q = p.val := hq
    have hs : q ∈ smoothAffineOverlapOpen W true true := by
      rw [smoothAffineOverlapOpen_eq]
      change integralProductOverlapFst W true true false false q ∈
        smoothProductChartOpen W true true
      rw [hq']
      exact p.property
    refine ⟨.affine, ⟨q, hs⟩, ?_⟩
    apply (smoothProductChartOpen W true true).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨q, hs⟩)
      (smoothAffineOverlapToChart_inclusion W true true)).trans hq'
  | polynomial =>
    have hq' : projectiveAdditionInclusion W 1 1 2 q = p.val := hq
    have hs : q ∈ polynomialSmoothInputOpen W 1 1 2 := by
      apply (polynomialSmoothInputOpen_preimage W true true 2).le
      change projectiveAdditionInclusion W 1 1 2 q ∈ smoothProductChartOpen W true true
      rw [hq']
      exact p.property
    refine ⟨.polynomial, ⟨q, hs⟩, ?_⟩
    apply (smoothProductChartOpen W true true).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨q, hs⟩)
      (smoothPolynomialToInputs_inclusion W true true 2)).trans hq'
  | infinity =>
    have hq' : infinityAdditionInclusion W q = p.val := hq
    have hs : q ∈ infinitySmoothInputOpen W := by
      rw [← infinitySmoothInputOpen_preimage]
      change infinityAdditionInclusion W q ∈ smoothProductChartOpen W true true
      rw [hq']
      exact p.property
    refine ⟨.infinity, ⟨q, hs⟩, ?_⟩
    apply (smoothProductChartOpen W true true).ι.isOpenEmbedding.injective
    exact (congrArg (fun f => f ⟨q, hs⟩)
      (smoothInfinityToInputs_inclusion W)).trans hq'

/-- A complete three-member open cover of the full smooth Y/Y product. -/
def smoothYCover : (smoothProductChartOpen W true true).toScheme.OpenCover where
  I₀ := YProductCoverIndex
  X := smoothYDomain W
  f := smoothYInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨smoothYInclusion_covers W, fun _ => inferInstance⟩

end FLT.Mazur.WeierstrassIntegralChart
