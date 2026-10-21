/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueAdjacentAnyDepthCoverage
public import FLT.Mazur.SchemePairDoubleBoundaryRange

/-!
# Nonpunctured smooth self-pairs on the adjacent chart

Both original inputs may have zero horizontal coordinate, including at creation
depth zero. Their full incidence intersection carries a scheme-valued transfer
with both new abscissas nonzero. The original two ambient inputs are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX IsLocalRing
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe v
variable {K : Type v} [Field K] (V : ValuationSubring K)
  {W : WeierstrassCurve V} {π : V} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => ResidueField V
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "eNext" => data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) 2
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "B" => PrincipalOpenTensor.transitionIso Q x u (previousBoundaryEquiv hπ e eNext)
local notation "a" => (A).inv ≫ PrincipalOpenTensor.inclusion Q t
local notation "b" => (B).inv ≫ PrincipalOpenTensor.inclusion Q u
local notation "old" => adjacentRetainedOldGlobalTensorChart hπ data Q j hj r hr
local notation "next" => olderGlobalTensorChart hπ data Q (j + 1) hjNext r hr
local notation "s" => pullback.fst
  (Spec.map (CommRingCat.ofHom (algebraMap V Q)))
  (finiteGlobalStructure hπ data (j + 2 + r) hr)
local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => adjacentRetainedGlobalTensor_isPullback hπ data Q j hj hjNext r hr

local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "hb" => (show a ≫ f = b ≫ f' from by
  simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w)

/-- The intersection of the two original incidence opens in the complete self-pair. -/
def residueAdjacentSelfBoundaryOpen : (pullback f f).Opens :=
  SchemePairDoubleBoundary.domain f f a a

local notation "O" => residueAdjacentSelfBoundaryOpen V hπ data j hj r hr

/-- The double domain is exactly the two original incidence nonvanishing conditions. -/
theorem residueAdjacentSelfBoundaryOpen_mem (p : (pullback f f : Scheme)) :
    p ∈ O ↔ tt ∉ (pullback.fst f f p).asIdeal ∧ tt ∉ (pullback.snd f f p).asIdeal := by
  change pullback.fst f f p ∈ Set.range a ∧ pullback.snd f f p ∈ Set.range a ↔ _
  have he := SchemeOpenChartRange.range_iso_comp (A).symm
    (PrincipalOpenTensor.inclusion Q t)
  exact and_congr
    ((congrArg (fun U => pullback.fst f f p ∈ U) he).to_iff.trans
      (PrincipalOpenTensor.mem_inclusion_range Q t _))
    ((congrArg (fun U => pullback.snd f f p ∈ U) he).to_iff.trans
      (PrincipalOpenTensor.mem_inclusion_range Q t _))

/-- Change both inputs on the entire original incidence intersection. -/
def residueAdjacentSelfBoundaryTransfer : (O).toScheme ⟶ pullback f' f' :=
  SchemePairDoubleBoundary.transfer f f' f f' a b a b hb hb

local notation "tr" => residueAdjacentSelfBoundaryTransfer V hπ data j hj hjNext r hr

/-- The first original ambient input survives both boundary changes. -/
@[reassoc] theorem residueAdjacentSelfBoundaryTransfer_first :
    tr ≫ pullback.fst f' f' ≫ next = (O).ι ≫ pullback.fst f f ≫ old :=
  SchemePairDoubleBoundary.transfer_first_ambient f f' f f' a b a b hb hb old next (H).w

/-- The second original ambient input survives both boundary changes. -/
@[reassoc] theorem residueAdjacentSelfBoundaryTransfer_second :
    tr ≫ pullback.snd f' f' ≫ next = (O).ι ≫ pullback.snd f f ≫ old :=
  SchemePairDoubleBoundary.transfer_second_ambient f f' f f' a b a b hb hb old next (H).w

/-- Both new abscissas are nonzero throughout the actual double boundary domain. -/
theorem residueAdjacentSelfBoundaryTransfer_punctured (p : (O).toScheme) :
    tu ∉ (pullback.fst f' f' (tr p)).asIdeal ∧
      tu ∉ (pullback.snd f' f' (tr p)).asIdeal := by
  have h₁ := SchemePairDoubleBoundary.transfer_fst_mem_range f f' f f' a b a b hb hb p
  have h₂ := SchemePairDoubleBoundary.transfer_snd_mem_range f f' f f' a b a b hb hb p
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  have hv' : tu ∉ (b v).asIdeal :=
    (PrincipalOpenTensor.mem_inclusion_range Q u _).mp ⟨_, rfl⟩
  have hw' : tu ∉ (b w).asIdeal :=
    (PrincipalOpenTensor.mem_inclusion_range Q u _).mp ⟨_, rfl⟩
  exact ⟨hv ▸ hv', hw ▸ hw'⟩

include D in
/-- Two smooth zero-abscissa inputs belong to the full simultaneous transfer domain. -/
theorem residueAdjacentSelfBoundaryOpen_anyDepth_zero_mem
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f f : Scheme))
    (hs₁ : old (pullback.fst f f p) ∈ (s).smoothLocus)
    (hs₂ : old (pullback.snd f f p) ∈ (s).smoothLocus)
    (hz₁ : oldU ∈ (pullback.fst f f p).asIdeal)
    (hz₂ : oldU ∈ (pullback.snd f f p).asIdeal) : p ∈ O := by
  apply (residueAdjacentSelfBoundaryOpen_mem V hπ data j hj r hr p).mpr
  have h₁ := residueAdjacentPairOpen_anyDepth_zero_mem V hπ data D j hj r hr f hk p hs₁ hz₁
  have h₂ := residueAdjacentPairOpen_anyDepth_zero_mem V hπ data D j hj r hr f hk
    ((pullbackSymmetry f f).hom p)
  rw [residueAdjacentPairOpen_mem] at h₁ h₂
  have he := congrArg (fun k => k p) (pullbackSymmetry_hom_comp_fst f f)
  change pullback.fst f f ((pullbackSymmetry f f).hom p) = pullback.snd f f p at he
  rw [he] at h₂
  exact ⟨h₁, h₂ hs₂ hz₂⟩

end FLT.Mazur.WeierstrassDividedDepth
