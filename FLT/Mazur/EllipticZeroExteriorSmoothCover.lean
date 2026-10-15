/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedBoundaryRange
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSlope
public import FLT.Mazur.WeierstrassSuccessiveXZeroSmoothCover

/-!
# Exact smooth coverage of the full retained exterior

The arithmetic horizontal boundary and the entire original conic boundary
together cover exactly the smooth restriction of a zero-depth exterior.
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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
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
local notation "c" => PrincipalOpenTensor.inclusion F t ≫ g

/-- The original incidence boundary is exactly D(t) in the full older tensor chart. -/
theorem zeroExteriorIncidenceOpen_mem_iff (z : Spec (.of T)) :
    g z ∈ Set.range c ↔ tt ∉ z.asIdeal := by
  have hi : g z ∈ Set.range (PrincipalOpenTensor.inclusion F t ≫ g) ↔
      z ∈ Set.range (PrincipalOpenTensor.inclusion F t) := by
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, (g).isOpenEmbedding.injective hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg g hx⟩
  exact hi.trans (PrincipalOpenTensor.mem_inclusion_range F t z)

include D hk0 hk in
/-- Both actual boundary opens cover all smooth points and contain no singular point. -/
theorem zeroExterior_smooth_boundary_cover :
    Set.range b ∪ Set.range c = Set.range g ∩
      (p).smoothLocus.carrier := by
  have hs (z : Spec (.of T)) :
      g z ∈ (p).smoothLocus ↔ tt ∉ z.asIdeal ∨ tu ∉ z.asIdeal :=
    zeroResidue_mem_smooth_iff D (start + j) hk0 hk (Data.b3 e) (Data.b4 e)
      (Data.b6 e) (Data.factor3 e) (Data.factor4 e) g p
      (olderGlobalTensorChart_structure hπ data F j hj r hr) z
  have hc : Set.range c ⊆ Set.range g := by
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
      (fun h => Or.inl ((zeroExteriorIncidenceOpen_mem_iff
        A hπ data j hj r hr x).mp h))
  · rintro ⟨⟨x, rfl⟩, hx⟩
    rcases (hs x).mp hx with hc | hb
    · exact Or.inr ((zeroExteriorIncidenceOpen_mem_iff
        A hπ data j hj r hr x).mpr hc)
    · exact Or.inl ((finiteRetainedBoundaryTensorChart_mem_iff
        A hπ data j hj r hr F x).mpr hb)

/-- The zero-depth arithmetic boundary is the whole original punctured slope chart. -/
theorem zeroRetainedBoundary_range_eq_slope :
    Set.range b = Set.range (olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk) := by
  let E := zeroResidueFiberIso D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
  have hmem (x : Spec (.of T)) : g x ∈ Set.range b ↔ tu ∉ x.asIdeal :=
    finiteRetainedBoundaryTensorChart_mem_iff A hπ data j hj r hr F x
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨x, rfl⟩ := finiteRetainedBoundaryTensorChart_range_subset A hπ data j hj r hr F hz
    obtain ⟨y, rfl⟩ := E.hom.homeomorph.surjective x
    have hy := (hmem (E.hom y)).mp hz
    change zeroResidueFiberEquiv D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) tu ∉ y.asIdeal at hy
    rw [zeroResidueFiberEquiv_u] at hy
    have hy' : y ∈ Set.range (WeierstrassModificationX.fiberExteriorSlopeChart
        (residue A W.a₁) (residue A (Data.b6 e))) := by
      rw [WeierstrassModificationX.fiberExteriorSlopeChart_range]
      exact hy
    obtain ⟨v, rfl⟩ := hy'
    exact ⟨v, rfl⟩
  · rintro z ⟨v, rfl⟩
    apply (hmem _).mpr
    change zeroResidueFiberEquiv D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) tu ∉
        (WeierstrassModificationX.fiberExteriorSlopeChart
          (residue A W.a₁) (residue A (Data.b6 e)) v).asIdeal
    rw [zeroResidueFiberEquiv_u]
    have hy : WeierstrassModificationX.fiberExteriorSlopeChart
        (residue A W.a₁) (residue A (Data.b6 e)) v ∈ Set.range
        (WeierstrassModificationX.fiberExteriorSlopeChart
          (residue A W.a₁) (residue A (Data.b6 e))) := ⟨v, rfl⟩
    rw [WeierstrassModificationX.fiberExteriorSlopeChart_range] at hy
    exact hy

include D hk0 hk in
/-- Every zero-depth arithmetic boundary point already belongs to the original infinity chart. -/
theorem zeroRetainedBoundary_range_subset_infinity :
    Set.range b ⊆ Set.range (finiteInfinityTensorChart hπ data F (j + 1 + r) hr) := by
  rw [zeroRetainedBoundary_range_eq_slope A hπ data D j hj r hr hk0 hk,
    ← olderGlobalZeroSlopeToInfinity_comp hπ data D j hj r hr hk0 hk]
  rintro z ⟨x, rfl⟩
  exact ⟨_, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
