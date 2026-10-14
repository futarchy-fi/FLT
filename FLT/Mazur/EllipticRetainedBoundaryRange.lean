/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryAtlas
public import FLT.Mazur.PrincipalOpenTensorRange

/-!
# Exact horizontal boundary inside the full retained tensor chart

The arithmetic retained boundary is precisely the principal open of the
original horizontal coordinate, after any coefficient extension.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (t : ℕ) (ht : j + 1 + t ≤ n)
  (S : Type u) [CommRing S] [Algebra A S]
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "C" => WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "T" => WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A S))
local notation "f" => finiteGlobalStructure hπ data (j + 1 + t) ht
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j hj t ht S
local notation "g" => olderGlobalTensorChart hπ data S j hj t ht
local notation "old" => olderGlobalChart hπ data j hj t ht
local notation "tu" => WeierstrassSuccessiveX.tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S 2

/-- The original preceding boundary is the whole horizontal principal open. -/
theorem retainedPreviousBoundary_range :
    Set.range (previousToX hπ d e) = (PrimeSpectrum.basicOpen u : Set (PrimeSpectrum C)) := by
  let H := WeierstrassSuccessiveX.horizontalIso W (π ^ (start + j)) π
    (Data.b3 e) (Data.b4 e) (Data.b6 e)
  let i := WeierstrassSuccessiveX.horizontalOpenInclusion W (π ^ (start + j)) π
    (Data.b3 e) (Data.b4 e) (Data.b6 e)
  exact (SchemeOpenChartRange.range_iso_comp (previousBoundaryIso hπ d e).symm
    (H.inv ≫ i)).trans ((SchemeOpenChartRange.range_iso_comp H.symm i).trans
      (PrimeSpectrum.localization_away_comap_range _ u))

/-- Within the full older tensor chart the arithmetic boundary is exactly D(u). -/
theorem finiteRetainedBoundaryTensorChart_mem_iff (z : Spec (.of T)) :
    g z ∈ Set.range b ↔ tu ∉ z.asIdeal := by
  change g z ∈ Set.range (TensorOpenChart.chart f _ _) ↔ _
  rw [TensorOpenChart.chart_range]
  change pullback.snd q f (g z) ∈
    Set.range (finiteRetainedBoundaryChart A hπ data j hj t ht) ↔ _
  have he := congrArg (fun m => m z)
    (retainedBoundaryAtlas_isPullback A hπ data j hj t ht S).w
  change pullback.snd q f (g z) = old (TensorOpenChart.projection z) at he
  rw [he]
  have hi : old (TensorOpenChart.projection z) ∈
      Set.range (finiteRetainedBoundaryChart A hπ data j hj t ht) ↔
      TensorOpenChart.projection z ∈ Set.range (previousToX hπ d e) := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (old).isOpenEmbedding.injective hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg old hx⟩
  rw [hi, retainedPreviousBoundary_range A hπ data j hj]
  rfl

/-- The whole retained tensor boundary is the horizontal principal open in its original chart. -/
theorem finiteRetainedBoundaryTensorChart_range :
    Set.range b = Set.range (PrincipalOpenTensor.inclusion S u ≫ g) := by
  have hu : Set.range (PrincipalOpenTensor.inclusion S u) =
      (PrimeSpectrum.basicOpen tu : Set (PrimeSpectrum T)) :=
    PrincipalOpenTensor.inclusion_range S u
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := finiteRetainedBoundaryTensorChart_range_subset
      A hπ data j hj t ht S hz
    have hx := (finiteRetainedBoundaryTensorChart_mem_iff A hπ data j hj t ht S x).mp hz
    have hx' : x ∈ Set.range (PrincipalOpenTensor.inclusion S u) := by
      rw [hu]
      exact hx
    obtain ⟨y, rfl⟩ := hx'
    exact ⟨y, rfl⟩
  · rintro z ⟨x, rfl⟩
    apply (finiteRetainedBoundaryTensorChart_mem_iff A hπ data j hj t ht S _).mpr
    have hx : PrincipalOpenTensor.inclusion S u x ∈
        Set.range (PrincipalOpenTensor.inclusion S u) := ⟨x, rfl⟩
    rw [hu] at hx
    exact hx

end FLT.Mazur.WeierstrassDividedDepth
