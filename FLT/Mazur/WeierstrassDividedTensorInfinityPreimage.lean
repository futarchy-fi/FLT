/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderInfinityPreimage
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedGlobalTensorInfinity
public import FLT.Mazur.WeierstrassDilatationResidueRetained

/-!
# Infinity on the full divided tensor chart

At every stage the infinity intersection is the original affine Y-open.
At exponent zero this is exactly the unscaled divided tensor Y-open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "c" => globalDividedTensorChart hπ data S j hj
local notation "i" => finiteInfinityTensorChart hπ data S j hj
local notation "p" => pullback.snd q (finiteGlobalStructure hπ data j hj)
open WeierstrassIntegralChart

/-- The original affine Y-boundary describes infinity at stage zero as well as later stages. -/
theorem finiteLocalChart_infinity_preimage_all :
    finiteLocalChart hπ data j hj ⁻¹' Set.range (finiteInfinityChart hπ data j hj) =
      (finiteToAffine hπ data j hj) ⁻¹' Set.range (overlapInclusion W 2 1) := by
  rw [finiteYBoundary_preimage]
  exact SchemeOpenPushout.inr_preimage_inl _ _

/-- The global divided tensor projection retains its original integral divided chart. -/
@[reassoc] theorem globalDividedTensorChart_projection :
    c ≫ p = TensorOpenChart.projection ≫
      (finiteExterior hπ data E₀ j hj).dividedChart ≫ finiteLocalChart hπ data j hj := by
  rw [globalDividedTensorChart, Category.assoc, finiteLocalTensorEmbedding_square]
  change TensorOpenChart.chart _ _ _ ≫ _ ≫ _ = _
  rw [TensorOpenChart.chart_snd_assoc]

/-- The complete divided chart meets infinity exactly over the original affine Y-open. -/
theorem globalDividedTensor_infinity_preimage :
    c ⁻¹' Set.range i = (TensorOpenChart.projection ≫ toAffine d) ⁻¹'
      (PrimeSpectrum.basicOpen (coord W 2 1) : Set (PrimeSpectrum (Coordinate W 2))) := by
  rw [finiteInfinityTensorChart_range]
  have he : c ⁻¹' (p ⁻¹' Set.range (finiteInfinityChart hπ data j hj)) =
      TensorOpenChart.projection ⁻¹'
        (((finiteExterior hπ data E₀ j hj).dividedChart ≫
          finiteLocalChart hπ data j hj) ⁻¹'
            Set.range (finiteInfinityChart hπ data j hj)) := by
    ext z
    change p (c z) ∈ Set.range (finiteInfinityChart hπ data j hj) ↔ _
    rw [show p (c z) = finiteLocalChart hπ data j hj
      ((finiteExterior hπ data E₀ j hj).dividedChart (TensorOpenChart.projection z)) from
        congrArg (fun f => f z) (globalDividedTensorChart_projection hπ data S j hj)]
    rfl
  rw [he]
  have hc := chart_preimage_of_contraction
    (B := finiteModification hπ data j hj)
    (finiteExterior hπ data E₀ j hj).dividedChart (finiteLocalChart hπ data j hj)
    _ _ _ _ (finiteLocalChart_infinity_preimage_all hπ data j hj)
    (finiteDivided_toAffine hπ data j hj)
  have hb : Set.range (overlapInclusion W 2 1) =
      (PrimeSpectrum.basicOpen (coord W 2 1) : Set (PrimeSpectrum (Coordinate W 2))) :=
    PrincipalAffineRefinement.range_inclusion _
  rw [hc, hb]
  rfl

/-- At exponent zero infinity is exactly the original divided tensor Y-open. -/
theorem globalDividedTensor_zero_infinity (hk : start + j = 0) :
    c ⁻¹' Set.range i =
      (PrimeSpectrum.basicOpen
        (WeierstrassDilatation.tensorY W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d) S) :
          Set (PrimeSpectrum
            (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
              (Data.b3 d) (Data.b4 d) (Data.b6 d) S))) := by
  rw [globalDividedTensor_infinity_preimage]
  ext z
  change (Algebra.TensorProduct.includeRight
    ((WeierstrassDilatation.fromOriginal W (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)) (coord W 2 1))) ∉ z.asIdeal ↔ _
  rw [WeierstrassDilatation.fromOriginal_y]
  simp only [hk, pow_zero, map_one, one_mul]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
