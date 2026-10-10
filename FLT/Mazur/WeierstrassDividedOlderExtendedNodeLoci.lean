/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalNodeComponents
public import FLT.Mazur.WeierstrassDividedOlderZeroExtendedGeometry

/-!
# Ordered positive-depth node loci over coefficient extensions

The two complete older nodes still cover their original chart after extension.
Their conic and ordered line loci are exactly the pullbacks of the original
U and Z vanishing loci. In particular the opposite tangent is not relabeled.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- A full chart pullback preserves the inverse image of any original component locus. -/
theorem residueExtension_chart_preimage {X Y A : Scheme.{u}}
    (p : Y ⟶ X) (g : A ⟶ X) (Z : Set X) :
    pullback.fst p g ⁻¹' (p ⁻¹' Z) = pullback.snd p g ⁻¹' (g ⁻¹' Z) := by
  change (pullback.fst p g ≫ p) ⁻¹' Z = (pullback.snd p g ≫ g) ⁻¹' Z
  rw [pullback.condition]

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c₀" => residue R (Data.b6 e)
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "t" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 0
local notation "v" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 1
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 2
local notation "c" => olderGlobalTensorChart hπ data K j hj r hr
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "N₁" => olderGlobalResidueFirstNode hπ data D j hj r hr hk0 hk
local notation "N₂" => olderGlobalResidueSecondNode hπ data D j hj r hr hk0 hk

/-- The two full positive-depth nodes still cover exactly their actual older chart. -/
theorem olderExtendedResidueNodes_range :
    Set.range (pullback.fst p N₁) ∪ Set.range (pullback.fst p N₂) =
      Set.range (pullback.fst p c) := by
  simp only [Scheme.Pullback.range_fst, ← Set.preimage_union, olderGlobalResidueNodes_range]

/-- The first node retains exactly the full extended conic locus U=0. -/
theorem olderExtendedResidueFirstNode_conicLocus :
    pullback.fst p N₁ ⁻¹' (p ⁻¹' (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T))) =
      pullback.snd p N₁ ⁻¹'
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [residueExtension_chart_preimage, olderGlobalResidueFirstNode_conicLocus]

/-- The opposite node retains the same full extended conic locus U=0. -/
theorem olderExtendedResidueSecondNode_conicLocus :
    pullback.fst p N₂ ⁻¹' (p ⁻¹' (c '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T))) =
      pullback.snd p N₂ ⁻¹'
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [residueExtension_chart_preimage, olderGlobalResidueSecondNode_conicLocus]

/-- The first node retains exactly its original ordered line, with t=v=0. -/
theorem olderExtendedResidueFirstNode_lineLocus :
    pullback.fst p N₁ ⁻¹'
        (p ⁻¹' (c '' PrimeSpectrum.zeroLocus (Ideal.span {t, v} : Set T))) =
      pullback.snd p N₁ ⁻¹'
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [residueExtension_chart_preimage, olderGlobalResidueFirstNode_lineLocus]

/-- The second node retains the opposite ordered tangent, with t=v+a₁=0. -/
theorem olderExtendedResidueSecondNode_lineLocus :
    pullback.fst p N₂ ⁻¹' (p ⁻¹' (c '' PrimeSpectrum.zeroLocus
        (Ideal.span {t, v + algebraMap K T (residue R W.a₁)} : Set T))) =
      pullback.snd p N₂ ⁻¹'
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c₀} : Set (MiddleNodeOpen c₀)) := by
  rw [residueExtension_chart_preimage, olderGlobalResidueSecondNode_lineLocus]

end FLT.Mazur.WeierstrassDividedDepth
