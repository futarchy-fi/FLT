/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodes
public import FLT.Mazur.WeierstrassSuccessiveXZeroNodeIdeals
public import FLT.Mazur.SpecChartIdealPreimage

/-!
# Original first component and node loci retained in every later model

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
  (r : ℕ) (hr : j + 1 + r ≤ n)
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
local notation "g₀" => olderGlobalTensorChart hπ data K j hj r hr
local notation "f₀" => zeroFirstNodeMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "f₁" => zeroSecondNodeMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)

/-- The first global node uses exactly the original tensor function map. -/
theorem olderGlobalZeroFirstNode_eq_spec :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk =
      Spec.map (CommRingCat.ofHom (f₀).toRingHom) ≫ g₀ := by
  rw [olderGlobalZeroFirstNode, olderGlobalZeroSuccessiveChart,
    fullFirstNodeChart_eq_spec, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The first actual global node keeps the original incidence locus. -/
theorem olderGlobalZeroFirstNode_incidenceLocus :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {t} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeP a c} : Set (FullNodeOpen a c)) := by
  rw [olderGlobalZeroFirstNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroFirstNodeMap_incidenceIdeal]

/-- The first actual global node keeps the original conic locus. -/
theorem olderGlobalZeroFirstNode_conicLocus :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeQ a c} : Set (FullNodeOpen a c)) := by
  rw [olderGlobalZeroFirstNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroFirstNodeMap_conicIdeal]

/-- The first actual global node keeps the original intersection locus. -/
theorem olderGlobalZeroFirstNode_intersectionLocus :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus
        ((Ideal.span {t} ⊔ Ideal.span {u} : Ideal T) : Set T)) =
        PrimeSpectrum.zeroLocus (fullNodeOriginIdeal a c : Set (FullNodeOpen a c)) := by
  rw [olderGlobalZeroFirstNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroFirstNodeMap_intersectionIdeal]

/-- The second global node uses exactly the original tensor function map. -/
theorem olderGlobalZeroSecondNode_eq_spec :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk =
      Spec.map (CommRingCat.ofHom (f₁).toRingHom) ≫ g₀ := by
  rw [olderGlobalZeroSecondNode, olderGlobalZeroSuccessiveChart,
    fullSecondNodeChart_eq_spec, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

/-- The second actual global node keeps the original incidence locus. -/
theorem olderGlobalZeroSecondNode_incidenceLocus :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {t} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeP (-a) c} : Set (FullNodeOpen (-a) c)) := by
  rw [olderGlobalZeroSecondNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroSecondNodeMap_incidenceIdeal]

/-- The second actual global node keeps the original conic locus. -/
theorem olderGlobalZeroSecondNode_conicLocus :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {fullNodeQ (-a) c} : Set (FullNodeOpen (-a) c)) := by
  rw [olderGlobalZeroSecondNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroSecondNodeMap_conicIdeal]

/-- The second actual global node keeps the original intersection locus. -/
theorem olderGlobalZeroSecondNode_intersectionLocus :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      (g₀ '' PrimeSpectrum.zeroLocus
        ((Ideal.span {t} ⊔ Ideal.span {u} : Ideal T) : Set T)) =
        PrimeSpectrum.zeroLocus (fullNodeOriginIdeal (-a) c : Set (FullNodeOpen (-a) c)) := by
  rw [olderGlobalZeroSecondNode_eq_spec, SpecChartIdeal.preimage_image_zeroLocus,
    zeroSecondNodeMap_intersectionIdeal]

end FLT.Mazur.WeierstrassDividedDepth
