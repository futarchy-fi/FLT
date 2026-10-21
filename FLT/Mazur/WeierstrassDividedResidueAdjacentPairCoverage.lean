/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentZeroAbscissa
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensorIntersection
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Smooth zero-abscissa inputs in actual residue pair domains

The full relative pair, with an arbitrary second input, admits the adjacent
chart transition on its incidence open. Every smooth zero-abscissa first
input belongs to this domain. The transferred point is a genuine relative
pair and keeps both original ambient inputs.
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
variable {Y : Scheme.{v}} (g : Y ⟶ Spec (.of (ResidueField V)))

/-- The whole incidence-open domain in the original older residue relative pair. -/
def residueAdjacentPairOpen : (pullback f g).Opens :=
  SchemePairBoundaryTransfer.domain f g a

local notation "O" => residueAdjacentPairOpen V hπ data j hj r hr g

/-- The pair domain is exactly the nonvanishing locus of the first incidence coordinate. -/
theorem residueAdjacentPairOpen_mem (p : (pullback f g : Scheme)) :
    p ∈ O ↔ tt ∉ (pullback.fst f g p).asIdeal := by
  change pullback.fst f g p ∈ Set.range a ↔ _
  have he := SchemeOpenChartRange.range_iso_comp (A).symm
    (PrincipalOpenTensor.inclusion Q t)
  exact (congrArg (fun U => pullback.fst f g p ∈ U) he).to_iff.trans
    (PrincipalOpenTensor.mem_inclusion_range Q t _)

/-- The original common boundary gives a scheme map to the next residue pair. -/
def residueAdjacentPairTransfer : (O).toScheme ⟶ pullback f' g :=
  SchemePairBoundaryTransfer.transfer f f' g a b (by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w)

local notation "transfer" => residueAdjacentPairTransfer V hπ data j hj hjNext r hr g

/-- Both actual first inputs agree in the resolved residue stage. -/
@[reassoc] theorem residueAdjacentPairTransfer_first :
    transfer ≫ pullback.fst f' g ≫ next = (O).ι ≫ pullback.fst f g ≫ old :=
  SchemePairBoundaryTransfer.transfer_first_ambient f f' g a b _ old next (H).w

/-- The second input retains its entire original morphism. -/
@[reassoc] theorem residueAdjacentPairTransfer_second :
    transfer ≫ pullback.snd f' g = (O).ι ≫ pullback.snd f g :=
  SchemePairBoundaryTransfer.transfer_snd f f' g a b _

/-- The new coordinates stay in the full horizontal puncture on the whole pair domain. -/
theorem residueAdjacentPairTransfer_punctured (p : (O).toScheme) :
    tu ∉ (pullback.fst f' g (transfer p)).asIdeal := by
  have he := congrArg (fun k => k p)
    (SchemePairBoundaryTransfer.transfer_fst f f' g a b (by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ s) (H).w))
  change pullback.fst f' g (transfer p) = b _ at he
  rw [he]
  exact (PrincipalOpenTensor.mem_inclusion_range Q u _).mp ⟨_, rfl⟩

include D in
/-- Smooth zero-abscissa first inputs belong to the actual pair transition domain. -/
theorem residueAdjacentPairOpen_zero_mem
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : tensorCoord W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2 ∈ (pullback.fst f g p).asIdeal) :
    p ∈ O := by
  apply (residueAdjacentPairOpen_mem V hπ data j hj r hr g p).mpr
  exact adjacentZeroAbscissa_incidence_nonzero V hπ data D j hj hk0 hk r hr _ hs hz

include D in
/-- Every smooth first input is punctured already or lies in the full adjacent pair domain. -/
theorem residueAdjacentPairOpen_smooth_cover
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus) :
    tensorCoord W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2 ∉ (pullback.fst f g p).asIdeal ∨ p ∈ O := by
  by_cases hz : tensorCoord W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2 ∈ (pullback.fst f g p).asIdeal
  · exact Or.inr (residueAdjacentPairOpen_zero_mem V hπ data D j hj r hr g hk0 hk p hs hz)
  · exact Or.inl hz

end FLT.Mazur.WeierstrassDividedDepth
