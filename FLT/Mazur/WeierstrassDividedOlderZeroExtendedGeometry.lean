/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroNodeBoundaries
public import FLT.Mazur.WeierstrassDividedOlderZeroExtendedOrigins
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Full first-component geometry after coefficient extension

The entire incidence line and conic still cover the retained first chart.
Both conic parameter charts are retained. Each signed node meets both global
boundaries in the full preimage of D(Q); the entire conic misses both boundaries.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Pulling back both maps retains the entire preimage of their intersection. -/
theorem residueExtension_boundary_preimage {X Y A B : Scheme.{u}}
    (p : Y ⟶ X) (g : A ⟶ X) (h : B ⟶ X) :
    pullback.fst p g ⁻¹' Set.range (pullback.fst p h) =
      pullback.snd p g ⁻¹' (g ⁻¹' Set.range h) := by
  rw [Scheme.Pullback.range_fst]
  change (pullback.fst p g ≫ p) ⁻¹' Set.range h =
    (pullback.snd p g ≫ g) ⁻¹' Set.range h
  rw [pullback.condition]

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
  (S : Type u) [CommRing S] [Algebra R S] [Algebra (ResidueField R) S]
  [IsScalarTower R (ResidueField R) S]
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "p" => globalResidueExtensionMap hπ data S (j + 1 + r) hr
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "N₁" => olderGlobalZeroFirstNode hπ data D j hj r hr hk0 hk
local notation "N₂" => olderGlobalZeroSecondNode hπ data D j hj r hr hk0 hk
local notation "C" => olderGlobalZeroConic hπ data D j hj r hr hk0 hk
local notation "I" => olderGlobalZeroIncidence hπ data D j hj r hr hk0 hk
local notation "E" => olderGlobalExteriorTensorChart hπ data K j hj r hr
local notation "J" => finiteInfinityTensorChart hπ data K (j + 1 + r) hr

/-- Extension retains the full closed incidence/conic decomposition of the original chart. -/
theorem olderZeroExtendedComponents_cover :
    Set.range (pullback.fst p I) ∪ Set.range (pullback.fst p C) =
      Set.range (pullback.fst p (olderGlobalTensorChart hπ data K j hj r hr)) := by
  simp only [Scheme.Pullback.range_fst, ← Set.preimage_union,
    olderGlobalZeroComponents_cover]

/-- Both rational parameter charts cover the entire conic after extension. -/
theorem olderZeroExtendedConicParameters_cover :
    Set.range (pullback.fst p
      (olderGlobalZeroConicFirstParameter hπ data D j hj r hr hk0 hk)) ∪
    Set.range (pullback.fst p
      (olderGlobalZeroConicSecondParameter hπ data D j hj r hr hk0 hk)) =
        Set.range (pullback.fst p C) := by
  simp only [Scheme.Pullback.range_fst, ← Set.preimage_union,
    olderGlobalZeroConicParameters_cover]

/-- The first extended node meets exterior in exactly the extended D(Q). -/
theorem olderZeroExtendedFirstNode_exterior_preimage :
    pullback.fst p N₁ ⁻¹' Set.range (pullback.fst p E) =
      pullback.snd p N₁ ⁻¹' (PrimeSpectrum.basicOpen (fullNodeQ a c) :
        Set (PrimeSpectrum (FullNodeOpen a c))) := by
  rw [residueExtension_boundary_preimage, olderGlobalZeroFirstNode_exterior_preimage]

/-- The first extended node meets infinity in that same full D(Q). -/
theorem olderZeroExtendedFirstNode_infinity_preimage :
    pullback.fst p N₁ ⁻¹' Set.range (pullback.fst p J) =
      pullback.snd p N₁ ⁻¹' (PrimeSpectrum.basicOpen (fullNodeQ a c) :
        Set (PrimeSpectrum (FullNodeOpen a c))) := by
  rw [residueExtension_boundary_preimage, olderGlobalZeroFirstNode_infinity_preimage]

/-- The opposite extended node retains its sign and full exterior boundary. -/
theorem olderZeroExtendedSecondNode_exterior_preimage :
    pullback.fst p N₂ ⁻¹' Set.range (pullback.fst p E) =
      pullback.snd p N₂ ⁻¹' (PrimeSpectrum.basicOpen (fullNodeQ (-a) c) :
        Set (PrimeSpectrum (FullNodeOpen (-a) c))) := by
  rw [residueExtension_boundary_preimage, olderGlobalZeroSecondNode_exterior_preimage]

/-- The opposite extended node retains the identical full infinity boundary. -/
theorem olderZeroExtendedSecondNode_infinity_preimage :
    pullback.fst p N₂ ⁻¹' Set.range (pullback.fst p J) =
      pullback.snd p N₂ ⁻¹' (PrimeSpectrum.basicOpen (fullNodeQ (-a) c) :
        Set (PrimeSpectrum (FullNodeOpen (-a) c))) := by
  rw [residueExtension_boundary_preimage, olderGlobalZeroSecondNode_infinity_preimage]

/-- Every branch of the extended conic misses the entire exterior boundary. -/
theorem olderZeroExtendedConic_exterior_preimage_empty :
    pullback.fst p C ⁻¹' Set.range (pullback.fst p E) = ∅ := by
  rw [residueExtension_boundary_preimage, olderGlobalZeroConic_exterior_preimage_empty,
    Set.preimage_empty]

/-- Every branch of the extended conic misses the entire infinity boundary. -/
theorem olderZeroExtendedConic_infinity_preimage_empty :
    pullback.fst p C ⁻¹' Set.range (pullback.fst p J) = ∅ := by
  rw [residueExtension_boundary_preimage, olderGlobalZeroConic_infinity_preimage_empty,
    Set.preimage_empty]

end FLT.Mazur.WeierstrassDividedDepth
