/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderIndexedIntersections
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Positive-depth residue charts have no infinity intersection

The original y function retains its uniformizer power. When that power
vanishes in the coefficient algebra, the full infinity intersection is
empty, including for nonreduced coefficient algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- The image of a composite chart is the image of the whole first chart range. -/
theorem infinity_chart_comp_range {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g) = g '' Set.range f := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨f a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R}
  (S : Type u) [CommRing S] [Algebra R S]

/-- At positive depth the full original y function vanishes on the uniformizer-zero fiber. -/
theorem successiveOriginalY_tensor_zero {k : ℕ} (e : Data W π (k + 1))
    (hS : algebraMap R S π = 0) (hk : 0 < k) :
    (1 : S) ⊗ₜ[R] successiveOriginalY e = 0 := by
  rw [successiveOriginalY, ← Algebra.smul_def, ← TensorProduct.smul_tmul,
    Algebra.smul_def, map_pow, hS, zero_pow (Nat.ne_of_gt hk), zero_mul,
    TensorProduct.zero_tmul]

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
  (hS : algebraMap R S π = 0) (hk : 0 < start + j)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => olderGlobalTensorChart hπ data S j hj r hr
local notation "i" => finiteInfinityTensorChart hπ data S (j + 1 + r) hr

include hS hk in
/-- The entire positive-depth chart has empty infinity preimage after residue extension. -/
theorem olderGlobalResidue_infinity_preimage_empty : c ⁻¹' Set.range i = ∅ := by
  rw [olderGlobalTensor_infinity_preimage]
  change Set.range (PrimeSpectrum.comap
    (algebraMap _ (Localization.Away ((1 : S) ⊗ₜ[R] successiveOriginalY e)))) = ∅
  rw [PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] successiveOriginalY e),
    successiveOriginalY_tensor_zero S e hS hk, PrimeSpectrum.basicOpen_zero]
  rfl

include hS hk in
/-- No component of a positive-depth retained residue chart meets the original infinity chart. -/
theorem olderGlobalResidue_infinity_disjoint : Disjoint (Set.range c) (Set.range i) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, rfl⟩ ha
  have h : a ∈ c ⁻¹' Set.range i := ha
  rw [olderGlobalResidue_infinity_preimage_empty S hπ data j hj r hr hS hk] at h
  exact h

include hj hS hk in
/-- The actual retained atlas index is disjoint from index zero at positive residue depth. -/
theorem olderIndexedResidue_infinity_disjoint :
    Disjoint (Set.range (globalTensorAtlasMap hπ data S (j + 1 + r) hr
      (Fin.succ ⟨r + 1, by omega⟩)))
      (Set.range (globalTensorAtlasMap hπ data S (j + 1 + r) hr 0)) := by
  have H := olderIndexedInfinity_preimage hπ data S j hj r hr
  have hz : Set.range (PrincipalOpenTensor.inclusion (R := R) S
      (successiveOriginalY e)) = ∅ := by
    change Set.range (PrimeSpectrum.comap
      (algebraMap _ (Localization.Away ((1 : S) ⊗ₜ[R] successiveOriginalY e)))) = ∅
    rw [PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] successiveOriginalY e),
      successiveOriginalY_tensor_zero S e hS hk, PrimeSpectrum.basicOpen_zero]
    rfl
  rw [infinity_chart_comp_range, hz, Set.image_empty] at H
  rw [Set.disjoint_left]
  rintro z ⟨a, rfl⟩ ha
  exact (Set.ext_iff.mp H a).mp ha

include hj hk in
/-- A split-node datum gives disjointness in the actual residue-field atlas without extra inputs. -/
theorem olderSplitNode_infinity_disjoint [IsLocalRing R] {depth : ℕ}
    (D : SplitNodeDepth W π depth) :
    Disjoint (Set.range (globalTensorAtlasMap hπ data (IsLocalRing.ResidueField R)
      (j + 1 + r) hr (Fin.succ ⟨r + 1, by omega⟩)))
      (Set.range (globalTensorAtlasMap hπ data (IsLocalRing.ResidueField R)
        (j + 1 + r) hr 0)) := by
  apply olderIndexedResidue_infinity_disjoint (IsLocalRing.ResidueField R)
    hπ data j hj r hr _ hk
  exact (IsLocalRing.residue_eq_zero_iff π).mpr
    (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)

end FLT.Mazur.WeierstrassDividedDepth
