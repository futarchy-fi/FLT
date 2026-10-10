/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroBoundaries
public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroSections
public import FLT.Mazur.WeierstrassModificationXFiberExteriorSlope

/-!
# The exact exterior and infinity boundaries on both ordered full nodes

Both original attachments meet each full ambient node in D(q), the complete
complement of its conic branch. This preserves both ordered nodes, the
original divided constant, and all retained global indices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- The original first ambient node has exactly its whole conic-complement boundary. -/
theorem zeroFirstNode_exterior_preimage {S : Type u} [CommRing S]
    (a c : S) (ha : IsUnit a) :
    WeierstrassModificationX.fullFirstNodeChart a c ha ⁻¹'
      (PrimeSpectrum.basicOpen (WeierstrassModificationX.fiberConicFactor a c) :
        Set (PrimeSpectrum (WeierstrassModificationX.FiberCoordinate a c))) =
      (PrimeSpectrum.basicOpen (WeierstrassModificationX.fullNodeQ a c) :
        Set (PrimeSpectrum (WeierstrassModificationX.FullNodeOpen a c))) := by
  rw [WeierstrassModificationX.fullFirstNodeChart_eq_spec]
  ext z
  change WeierstrassModificationX.fiberFullFirstNodeMap a c ha
    (WeierstrassModificationX.fiberConicFactor a c) ∉ z.asIdeal ↔
      WeierstrassModificationX.fullNodeQ a c ∉ z.asIdeal
  rw [WeierstrassModificationX.fiberFullFirstNodeMap_conic,
    z.isPrime.mul_mem_iff_mem_or_mem]
  simp only [z.asIdeal.notMem_of_isUnit
    (WeierstrassModificationX.fullNodeInverseV_add_isUnit a c), or_false]

/-- The original second ambient node has exactly its whole conic-complement boundary. -/
theorem zeroSecondNode_exterior_preimage {S : Type u} [CommRing S]
    (a c : S) (ha : IsUnit a) :
    WeierstrassModificationX.fullSecondNodeChart a c ha ⁻¹'
      (PrimeSpectrum.basicOpen (WeierstrassModificationX.fiberConicFactor a c) :
        Set (PrimeSpectrum (WeierstrassModificationX.FiberCoordinate a c))) =
      (PrimeSpectrum.basicOpen (WeierstrassModificationX.fullNodeQ (-a) c) :
        Set (PrimeSpectrum (WeierstrassModificationX.FullNodeOpen (-a) c))) := by
  rw [WeierstrassModificationX.fullSecondNodeChart_eq_spec]
  ext z
  change WeierstrassModificationX.fiberFullSecondNodeMap a c ha
    (WeierstrassModificationX.fiberConicFactor a c) ∉ z.asIdeal ↔
      WeierstrassModificationX.fullNodeQ (-a) c ∉ z.asIdeal
  rw [WeierstrassModificationX.fiberFullSecondNodeMap_conic,
    z.isPrime.mul_mem_iff_mem_or_mem]
  simp only [z.asIdeal.notMem_of_isUnit
    (WeierstrassModificationX.fullNodeInverseV_add_isUnit (-a) c), or_false]

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The full exterior preimage at the retained first ordered node. -/
theorem olderGlobalZeroFirstNode_exterior_preimage :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) =
        (PrimeSpectrum.basicOpen (fullNodeQ a c) :
          Set (PrimeSpectrum (FullNodeOpen a c))) := by
  rw [olderGlobalZeroFirstNode, chart_comp_preimage,
    olderGlobalZeroExterior_preimage]
  exact zeroFirstNode_exterior_preimage a c ha

/-- The full infinity preimage at the retained first ordered node. -/
theorem olderGlobalZeroFirstNode_infinity_preimage :
    olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) =
        (PrimeSpectrum.basicOpen (fullNodeQ a c) :
          Set (PrimeSpectrum (FullNodeOpen a c))) := by
  rw [olderGlobalZeroFirstNode, chart_comp_preimage,
    olderGlobalZeroInfinity_preimage, fiberExterior_infinity_open]
  exact zeroFirstNode_exterior_preimage a c ha

/-- The full exterior preimage at the retained second ordered node. -/
theorem olderGlobalZeroSecondNode_exterior_preimage :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) =
        (PrimeSpectrum.basicOpen (fullNodeQ (-a) c) :
          Set (PrimeSpectrum (FullNodeOpen (-a) c))) := by
  rw [olderGlobalZeroSecondNode, chart_comp_preimage,
    olderGlobalZeroExterior_preimage]
  exact zeroSecondNode_exterior_preimage a c ha

/-- The full infinity preimage at the retained second ordered node. -/
theorem olderGlobalZeroSecondNode_infinity_preimage :
    olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) =
        (PrimeSpectrum.basicOpen (fullNodeQ (-a) c) :
          Set (PrimeSpectrum (FullNodeOpen (-a) c))) := by
  rw [olderGlobalZeroSecondNode, chart_comp_preimage,
    olderGlobalZeroInfinity_preimage, fiberExterior_infinity_open]
  exact zeroSecondNode_exterior_preimage a c ha

/-- The full first-fiber preimages of infinity and the preceding exterior coincide. -/
theorem olderGlobalZero_boundary_preimages_eq :
    g ⁻¹' Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) =
      g ⁻¹' Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) := by
  rw [olderGlobalZeroInfinity_preimage, olderGlobalZeroExterior_preimage,
    fiberExterior_infinity_open]

/-- The first ordered node section is absent from the exterior attachment. -/
theorem olderGlobalZeroFirstSection_exterior_preimage_empty :
    olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) = ∅ := by
  rw [← olderGlobalZeroFirstNode_origin, chart_comp_preimage,
    olderGlobalZeroFirstNode_exterior_preimage]
  ext z
  change fullNodeOrigin a c ha (fullNodeQ a c) ∉ z.asIdeal ↔ False
  rw [fullNodeOrigin_q]
  simp only [Ideal.zero_mem, not_true_eq_false]

/-- The first ordered node section is absent from the infinity attachment. -/
theorem olderGlobalZeroFirstSection_infinity_preimage_empty :
    olderGlobalZeroFirstSection hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) = ∅ := by
  rw [← olderGlobalZeroFirstNode_origin, chart_comp_preimage,
    olderGlobalZeroFirstNode_infinity_preimage]
  ext z
  change fullNodeOrigin a c ha (fullNodeQ a c) ∉ z.asIdeal ↔ False
  rw [fullNodeOrigin_q]
  simp only [Ideal.zero_mem, not_true_eq_false]

/-- The second ordered node section is absent from the exterior attachment. -/
theorem olderGlobalZeroSecondSection_exterior_preimage_empty :
    olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) = ∅ := by
  rw [← olderGlobalZeroSecondNode_origin, chart_comp_preimage,
    olderGlobalZeroSecondNode_exterior_preimage]
  ext z
  change fullNodeOrigin (-a) c (ha).neg (fullNodeQ (-a) c) ∉ z.asIdeal ↔ False
  rw [fullNodeOrigin_q]
  simp only [Ideal.zero_mem, not_true_eq_false]

/-- The second ordered node section is absent from the infinity attachment. -/
theorem olderGlobalZeroSecondSection_infinity_preimage_empty :
    olderGlobalZeroSecondSection hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) = ∅ := by
  rw [← olderGlobalZeroSecondNode_origin, chart_comp_preimage,
    olderGlobalZeroSecondNode_infinity_preimage]
  ext z
  change fullNodeOrigin (-a) c (ha).neg (fullNodeQ (-a) c) ∉ z.asIdeal ↔ False
  rw [fullNodeOrigin_q]
  simp only [Ideal.zero_mem, not_true_eq_false]

/-- The entire retained conic is disjoint from the original exterior boundary. -/
theorem olderGlobalZeroConic_exterior_preimage_empty :
    olderGlobalZeroConic hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) = ∅ := by
  rw [olderGlobalZeroConic, chart_comp_preimage,
    olderGlobalZeroExterior_preimage]
  ext z
  change fiberConicMap a c (fiberConicFactor a c) ∉ z.asIdeal ↔ False
  rw [fiberConicMap_factor]
  simp only [Ideal.zero_mem, not_true_eq_false]

/-- The incidence line meets exterior in exactly the complement of both ordered roots. -/
theorem olderGlobalZeroIncidence_exterior_preimage :
    olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) =
        (PrimeSpectrum.basicOpen (slopePolynomial a) : Set (PrimeSpectrum (Polynomial K))) := by
  rw [olderGlobalZeroIncidence, chart_comp_preimage,
    olderGlobalZeroExterior_preimage]
  ext z
  change fiberIncidenceMap a c (fiberConicFactor a c) ∉ z.asIdeal ↔ _
  rw [fiberIncidenceMap_factor]
  rfl

/-- The entire retained conic is disjoint from the original infinity boundary. -/
theorem olderGlobalZeroConic_infinity_preimage_empty :
    olderGlobalZeroConic hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) = ∅ := by
  rw [olderGlobalZeroConic, chart_comp_preimage,
    olderGlobalZeroInfinity_preimage, fiberExterior_infinity_open]
  ext z
  change fiberConicMap a c (fiberConicFactor a c) ∉ z.asIdeal ↔ False
  rw [fiberConicMap_factor]
  simp only [Ideal.zero_mem, not_true_eq_false]

/-- The incidence line meets infinity in exactly the complement of both ordered roots. -/
theorem olderGlobalZeroIncidence_infinity_preimage :
    olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk ⁻¹'
      Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) =
        (PrimeSpectrum.basicOpen (slopePolynomial a) : Set (PrimeSpectrum (Polynomial K))) := by
  rw [olderGlobalZeroIncidence, chart_comp_preimage,
    olderGlobalZeroInfinity_preimage, fiberExterior_infinity_open]
  ext z
  change fiberIncidenceMap a c (fiberConicFactor a c) ∉ z.asIdeal ↔ _
  rw [fiberIncidenceMap_factor]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
