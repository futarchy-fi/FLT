/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalZeroNodes
public import FLT.Mazur.WeierstrassSuccessiveXZeroNodeIdeals
public import FLT.Mazur.SpecChartIdealPreimage

/-!
# Original component and node loci in the first global successive chart

The two ordered node immersions retain the original tensor component ideals
and their full scheme-theoretic intersection inside the actual global atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
open WeierstrassModificationX

local notation "T" => WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "t" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 0
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 2
local notation "g₀" => globalSuccessiveTensorChart hπ data K j hj
local notation "f₀" => zeroFirstNodeMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "f₁" => zeroSecondNodeMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The first global node uses exactly the original tensor function map. -/
theorem globalZeroFirstNode_eq_spec :
    globalZeroFirstNode hπ data D j hj hk0 hk =
      Spec.map (CommRingCat.ofHom (f₀).toRingHom) ≫ g₀ := by
  rw [globalZeroFirstNode, globalZeroSuccessiveChart,
    fullFirstNodeChart_eq_spec, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The first actual global node keeps the original incidence locus. -/
theorem globalZeroFirstNode_incidenceLocus :
    globalZeroFirstNode hπ data D j hj hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {t} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeP a c} : Set (FullNodeOpen a c)) := by
  rw [globalZeroFirstNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroFirstNodeMap_incidenceIdeal]

/-- The first actual global node keeps the original conic locus. -/
theorem globalZeroFirstNode_conicLocus :
    globalZeroFirstNode hπ data D j hj hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeQ a c} : Set (FullNodeOpen a c)) := by
  rw [globalZeroFirstNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroFirstNodeMap_conicIdeal]

/-- The first actual global node keeps the original intersection locus. -/
theorem globalZeroFirstNode_intersectionLocus :
    globalZeroFirstNode hπ data D j hj hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus
        ((Ideal.span {t} ⊔ Ideal.span {u} : Ideal T) : Set T)) =
        PrimeSpectrum.zeroLocus (fullNodeOriginIdeal a c : Set (FullNodeOpen a c)) := by
  rw [globalZeroFirstNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroFirstNodeMap_intersectionIdeal]

/-- The second global node uses exactly the original tensor function map. -/
theorem globalZeroSecondNode_eq_spec :
    globalZeroSecondNode hπ data D j hj hk0 hk =
      Spec.map (CommRingCat.ofHom (f₁).toRingHom) ≫ g₀ := by
  rw [globalZeroSecondNode, globalZeroSuccessiveChart,
    fullSecondNodeChart_eq_spec, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second actual global node keeps the original incidence locus. -/
theorem globalZeroSecondNode_incidenceLocus :
    globalZeroSecondNode hπ data D j hj hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {t} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeP (-a) c} : Set (FullNodeOpen (-a) c)) := by
  rw [globalZeroSecondNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroSecondNodeMap_incidenceIdeal]

/-- The second actual global node keeps the original conic locus. -/
theorem globalZeroSecondNode_conicLocus :
    globalZeroSecondNode hπ data D j hj hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeQ (-a) c} : Set (FullNodeOpen (-a) c)) := by
  rw [globalZeroSecondNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroSecondNodeMap_conicIdeal]

/-- The second actual global node keeps the original intersection locus. -/
theorem globalZeroSecondNode_intersectionLocus :
    globalZeroSecondNode hπ data D j hj hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus
        ((Ideal.span {t} ⊔ Ideal.span {u} : Ideal T) : Set T)) =
        PrimeSpectrum.zeroLocus (fullNodeOriginIdeal (-a) c : Set (FullNodeOpen (-a) c)) := by
  rw [globalZeroSecondNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroSecondNodeMap_intersectionIdeal]

end FLT.Mazur.WeierstrassDividedDepth
