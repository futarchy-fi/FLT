/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryRange
public import FLT.Mazur.WeierstrassDividedOlderGlobalConicBoundary
public import FLT.Mazur.WeierstrassSuccessiveXResidueSmoothCover

/-!
# Exact smooth coverage of the full retained exterior

The arithmetic horizontal boundary and the entire original conic boundary
together cover exactly the smooth restriction of a positive-depth exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "F" => ResidueField A
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 0
local notation "tu" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) F 2
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap A F))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1 + r) hr)
local notation "g" => olderGlobalTensorChart hπ data F j hj r hr
local notation "b" => finiteRetainedBoundaryTensorChart A hπ data j hj r hr F
local notation "c" => olderGlobalConicBoundary hπ data D j hj r hr hk0 hk

/-- The full conic boundary is exactly the other principal open of the older tensor chart. -/
theorem olderGlobalConicBoundary_mem_iff (z : Spec (.of T)) :
    g z ∈ Set.range c ↔ tt ∉ z.asIdeal := by
  rw [← olderGlobalConicBoundary_transition hπ data D j hj r hr hk0 hk,
    SchemeOpenChartRange.range_iso_comp]
  have hi : g z ∈ Set.range (PrincipalOpenTensor.inclusion F t ≫ g) ↔
      z ∈ Set.range (PrincipalOpenTensor.inclusion F t) := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (g).isOpenEmbedding.injective hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg g hx⟩
  exact hi.trans (PrincipalOpenTensor.mem_inclusion_range F t z)

/-- Both actual boundary opens cover all smooth points and contain no singular point. -/
theorem retainedExterior_smooth_boundary_cover :
    Set.range b ∪ Set.range c = Set.range g ∩
      (p).smoothLocus.carrier := by
  have hs (z : Spec (.of T)) :
      g z ∈ (p).smoothLocus ↔ tt ∉ z.asIdeal ∨ tu ∉ z.asIdeal :=
    residueMiddle_mem_smooth_iff D (start + j) hk0 hk (Data.b3 e) (Data.b4 e)
      (Data.b6 e) (Data.factor3 e) (Data.factor4 e) g p
      (olderGlobalTensorChart_structure hπ data F j hj r hr) z
  have hc : Set.range c ⊆ Set.range g := by
    rw [← olderGlobalConicBoundary_transition hπ data D j hj r hr hk0 hk]
    rintro z ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  ext z
  constructor
  · intro hz
    have hz' : z ∈ Set.range g := by
      rcases hz with hb | hconic
      · exact finiteRetainedBoundaryTensorChart_range_subset A hπ data j hj r hr F hb
      · exact hc hconic
    obtain ⟨x, rfl⟩ := hz'
    refine ⟨⟨x, rfl⟩, (hs x).mpr ?_⟩
    exact hz.elim
      (fun h => Or.inr ((finiteRetainedBoundaryTensorChart_mem_iff
        A hπ data j hj r hr F x).mp h))
      (fun h => Or.inl ((olderGlobalConicBoundary_mem_iff
        A hπ data D j hj r hr hk0 hk x).mp h))
  · rintro ⟨⟨x, rfl⟩, hx⟩
    rcases (hs x).mp hx with hc | hb
    · exact Or.inr ((olderGlobalConicBoundary_mem_iff
        A hπ data D j hj r hr hk0 hk x).mpr hc)
    · exact Or.inl ((finiteRetainedBoundaryTensorChart_mem_iff
        A hπ data j hj r hr F x).mpr hb)

end FLT.Mazur.WeierstrassDividedDepth
