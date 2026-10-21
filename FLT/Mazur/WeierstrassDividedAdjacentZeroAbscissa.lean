/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdjacentRetainedBoundaryCover
public import FLT.Mazur.WeierstrassSuccessiveXResidueSmoothCover

/-!
# Smooth zero-abscissa inputs have adjacent punctured coordinates

Use the common retained stage to avoid dependent casts between presentations
of its index. The full input chart is preserved, and its zero-abscissa smooth
points acquire actual coordinates in the next retained horizontal puncture.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "F" => ResidueField A
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "eNext" => data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F
local notation "TNext" => ScalarExtension W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) F
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 2
local notation "uNext" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) F 2
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 0
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 2 + r) hr)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data F j hj r hr
local notation "gNext" => olderGlobalTensorChart hπ data F (j + 1) hjNext r hr
local notation "bNext" => finiteRetainedBoundaryTensorChart A hπ data (j + 1) hjNext r hr F
local notation "c" => adjacentRetainedConicBoundary hπ data D j hj hk0 hk r hr
local notation "E" => residueConicBoundaryIso D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The reassociated original chart preserves its coefficient structure. -/
@[reassoc] theorem adjacentZeroAbscissa_chart_structure :
    g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F T)) := by
  simp only [adjacentRetainedOldGlobalTensorChart, Category.assoc,
    finiteLocalTensorEmbedding_structure, adjacentRetainedOldTensorChart,
    TensorOpenChart.chart_fst]
  rfl

/-- The common-stage chart retains its original open immersion. -/
instance adjacentZeroAbscissa_chart_open : IsOpenImmersion g := by
  let _ : IsOpenImmersion (adjacentRetainedOldChart hπ data j hj r hr) := by
    unfold adjacentRetainedOldChart
    infer_instance
  unfold adjacentRetainedOldGlobalTensorChart adjacentRetainedOldTensorChart
  infer_instance

include D hk0 hk

/-- Smoothness forces the incidence coordinate to be nonzero when the abscissa vanishes. -/
theorem adjacentZeroAbscissa_incidence_nonzero (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) : tt ∉ z.asIdeal := by
  have h := (residueMiddle_mem_smooth_iff D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) g p
    (adjacentZeroAbscissa_chart_structure A hπ data j hj r hr) z).mp hs
  exact h.resolve_right (not_not.mpr hz)

/-- The full conic boundary sends a zero-abscissa smooth input to the next retained boundary. -/
theorem adjacentZeroAbscissa_mem_next (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) : g z ∈ Set.range bNext := by
  have ht := adjacentZeroAbscissa_incidence_nonzero A hπ data D j hj hk0 hk r hr z hs hz
  have hc : g z ∈ Set.range c := by
    rw [adjacentRetainedConicBoundary, SchemeOpenChartRange.range_iso_comp]
    obtain ⟨w, hw⟩ := (PrincipalOpenTensor.mem_inclusion_range F t z).mpr ht
    exact ⟨w, congrArg g hw⟩
  rwa [adjacentRetainedConicBoundary_range_eq_retained
    A hπ data D j hj hk0 hk hjNext r hr] at hc

/-- The same global input has actual next-chart coordinates with nonzero preceding abscissa. -/
theorem adjacentZeroAbscissa_next_coordinates (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) :
    ∃ w : Spec (.of TNext), gNext w = g z ∧ uNext ∉ w.asIdeal := by
  have hb := adjacentZeroAbscissa_mem_next A hπ data D j hj hk0 hk hjNext r hr z hs hz
  obtain ⟨w, hw⟩ := finiteRetainedBoundaryTensorChart_range_subset
    A hπ data (j + 1) hjNext r hr F hb
  refine ⟨w, hw, ?_⟩
  apply (finiteRetainedBoundaryTensorChart_mem_iff A hπ data (j + 1) hjNext r hr F w).mp
  rwa [hw]

end FLT.Mazur.WeierstrassDividedDepth
