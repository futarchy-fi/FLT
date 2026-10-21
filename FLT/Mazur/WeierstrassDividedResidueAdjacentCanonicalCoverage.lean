/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueAdjacentPairCoverage
public import FLT.Mazur.WeierstrassDividedTensorIntegralRelativeSmooth
public import FLT.Mazur.WeierstrassDividedAdjacentTensorSmooth

/-!
# Adjacent residue coverage with the canonical full indexed representative

The original retained tensor source supplies its own indexed representative
at every later stage. No equality to a separately chosen point is required.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  retainedTensorAtlasIso finiteTensorAtlasObject globalSmoothAtlasOpen
  tensorIntegralAtlasSmoothOpen
universe u
/-- Equality of scheme-open preimages identifies the corresponding pointwise tests. -/
theorem adjacentSmooth_mem_of_preimage_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (U : Y.Opens) (V : Z.Opens)
    (h : f ⁻¹ᵁ U = g ⁻¹ᵁ V) (p : X) : f p ∈ U ↔ g p ∈ V := by
  change p ∈ (f ⁻¹ᵁ U) ↔ p ∈ (g ⁻¹ᵁ V)
  rw [h]

section ArbitraryCoefficients
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "iso" => retainedTensorAtlasIso hπ data S (j + 2 + r) hr j (by omega)
local notation "idx" => (Fin.succ ⟨j + 2 + r - j, by omega⟩ : Fin (j + 2 + r + 3))
local notation "old" => adjacentRetainedOldGlobalTensorChart hπ data S j hj r hr
local notation "s" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  (finiteGlobalStructure hπ data (j + 2 + r) hr)

/-- The retained comparison with its target declared as the full global indexed chart. -/
def adjacentFullTensorAtlasIso :
    Spec (.of (ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) S)) ≅
      globalTensorAtlasObject hπ data S (j + 2 + r) hr idx := iso

attribute [local irreducible] adjacentFullTensorAtlasIso

omit [IsNoetherianRing R] in
/-- The explicitly global source comparison retains the entire original map. -/
@[reassoc] theorem adjacentFullTensorAtlasIso_map :
    (adjacentFullTensorAtlasIso hπ data S j hj r hr).hom ≫
      globalTensorAtlasMap hπ data S (j + 2 + r) hr idx = old := by
  unfold adjacentFullTensorAtlasIso
  exact retainedTensorAtlasIso_adjacent_map hπ data S j hj r hr

/-- The global indexed representative tests the original input's full relative smoothness. -/
theorem retainedTensorAtlasIso_adjacent_smooth_mem (p : Spec (.of (ScalarExtension W
    (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) S))) :
    (adjacentFullTensorAtlasIso hπ data S j hj r hr).hom p ∈
      tensorIntegralAtlasSmoothOpen hπ data S (j + 2 + r) hr idx ↔
      old p ∈ (s).smoothLocus := by
  apply adjacentSmooth_mem_of_preimage_eq
  rw [tensorIntegralAtlasSmoothOpen_relative, ← Scheme.Hom.comp_preimage,
    adjacentFullTensorAtlasIso_map]

end ArbitraryCoefficients

universe v
variable {K : Type v} [Field K] (V : ValuationSubring K) [IsNoetherianRing V]
  {W : WeierstrassCurve V} {π : V} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "Q" => ResidueField V
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "old" => adjacentRetainedOldGlobalTensorChart hπ data Q j hj r hr
local notation "s" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap V Q)))
  (finiteGlobalStructure hπ data (j + 2 + r) hr)
local notation "idx" => (Fin.succ ⟨j + 2 + r - j, by omega⟩ : Fin (j + 2 + r + 3))
local notation "iso" => adjacentFullTensorAtlasIso hπ data Q j hj r hr
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 2 + r) hr idx

/-- Canonical indexed smoothness is exactly relative smoothness of the original input. -/
theorem residueAdjacentCanonicalSource_smooth (p : Spec (.of (ScalarExtension W
    (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) Q))) :
    (iso).hom p ∈ O ↔ old p ∈ (s).smoothLocus := by
  exact retainedTensorAtlasIso_adjacent_smooth_mem hπ data Q j hj r hr p

variable {Y : Scheme.{v}} (g : Y ⟶ Spec (.of (ResidueField V)))
local notation "f" => old ≫ s
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

include D in
/-- Zero abscissa in the full canonical smooth domain lies in the actual adjacent boundary. -/
theorem residueAdjacentPairOpen_zero_mem_of_canonicalSmooth
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : (iso).hom (pullback.fst f g p) ∈ O)
    (hz : u ∈ (pullback.fst f g p).asIdeal) :
    p ∈ residueAdjacentPairOpen V hπ data j hj r hr g :=
  residueAdjacentPairOpen_zero_mem V hπ data D j hj r hr g hk0 hk p
    ((residueAdjacentCanonicalSource_smooth V hπ data j hj r hr _).mp hs) hz

include D in
/-- The puncture and actual adjacent boundary cover the entire canonical smooth first input. -/
theorem residueAdjacentPairOpen_cover_of_canonicalSmooth
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : (iso).hom (pullback.fst f g p) ∈ O) :
    u ∉ (pullback.fst f g p).asIdeal ∨ p ∈ residueAdjacentPairOpen V hπ data j hj r hr g :=
  residueAdjacentPairOpen_smooth_cover V hπ data D j hj r hr g hk0 hk p
    ((residueAdjacentCanonicalSource_smooth V hπ data j hj r hr _).mp hs)

end FLT.Mazur.WeierstrassDividedDepth
