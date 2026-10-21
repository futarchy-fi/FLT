/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedSmoothBoundaryCover

/-!
# Zero preceding abscissae lie in the full conic boundary

A smooth closed-fiber point of an older chart whose preceding abscissa
vanishes lies in the conic overlap, where its incidence coordinate is
nonzero. The original point remains in the complete input cover.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  olderGlobalTensorChart finiteRetainedBoundaryTensorChart olderGlobalConicBoundary
  WeierstrassSuccessiveX.ScalarExtension WeierstrassSuccessiveX.tensorCoord
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (r : ℕ) (hr : j + 1 + r ≤ n)
open WeierstrassSuccessiveX
local notation "F" => ResidueField A
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 2
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1 + r) hr)
local notation "g" => olderGlobalTensorChart hπ data F j hj r hr
local notation "c" => olderGlobalConicBoundary hπ data D j hj r hr hk0 hk
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 0

include D hk0 hk

/-- Every smooth zero-abscissa input is retained by the full conic overlap. -/
theorem retainedZeroAbscissa_mem_conic (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) : g z ∈ Set.range c := by
  have hcover := retainedExterior_smooth_boundary_cover A hπ data D j hj r hr hk0 hk
  have hmem : g z ∈ Set.range g ∩ (p).smoothLocus.carrier := ⟨⟨z, rfl⟩, hs⟩
  have hmem' := (Set.ext_iff.mp hcover (g z)).mpr hmem
  rcases hmem' with hb | hc
  · exact False.elim (((finiteRetainedBoundaryTensorChart_mem_iff
      A hπ data j hj r hr F z).mp hb) hz)
  · exact hc

/-- The incidence coordinate is nonzero at every such boundary input. -/
theorem retainedZeroAbscissa_incidence_nonzero (z : Spec (.of T))
    (hs : g z ∈ (p).smoothLocus) (hz : u ∈ z.asIdeal) : tt ∉ z.asIdeal :=
  (olderGlobalConicBoundary_mem_iff A hπ data D j hj r hr hk0 hk z).mp
    (retainedZeroAbscissa_mem_conic A hπ data D j hj hk0 hk r hr z hs hz)

end FLT.Mazur.WeierstrassDividedDepth
