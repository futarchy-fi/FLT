/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueTerminalPairCoverage
public import FLT.Mazur.WeierstrassDividedTensorIntegralRelativeSmooth
public import FLT.Mazur.WeierstrassDividedArithmeticNewestIndex

/-!
# Terminal residue boundary coverage on the exact indexed smooth domain

The original newest residue chart is the full retained indexed tensor chart.
Its exact integral smooth preimage supplies the relative smoothness required
by zero-abscissa boundary coverage; no puncture is removed in advance.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  olderSuccessiveTensorAtlasIso finiteTensorAtlasObject globalSmoothAtlasOpen
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [IsLocalRing R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => ResidueField R
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "old" => globalSuccessiveTensorChart hπ data Q j hj
local notation "s" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
  (finiteGlobalStructure hπ data (j + 1) hj)
local notation "idx" => (Fin.succ ⟨1, by omega⟩ : Fin (j + 1 + 3))
local notation "iso" => olderSuccessiveTensorAtlasIso hπ data Q j hj 0 hj
local notation "chart" => globalTensorAtlasMap hπ data Q (j + 1) hj idx
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj idx

omit [IsNoetherianRing R] in
/-- The newest residue source is exactly its full retained indexed chart. -/
@[reassoc] theorem residueTerminalIndexedSource_map : (iso).hom ≫ chart = old := by
  rw [olderGlobalTensorChart_eq_index]
  unfold olderGlobalTensorChart globalSuccessiveTensorChart
  rw [olderSuccessiveTensorChart_zero_eq_newest]

/-- The indexed full smooth domain is exactly the relative smoothness test on the old input. -/
theorem residueTerminalIndexedSource_smooth (p : Spec (.of (ScalarExtension W
    (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) Q))) :
    (iso).hom p ∈ O ↔ old p ∈ (s).smoothLocus := by
  rw [tensorIntegralAtlasSmoothOpen_mem_relative]
  have he := congrArg (fun f => f p) (residueTerminalIndexedSource_map hπ data j hj)
  exact he ▸ Iff.rfl

variable {Y : Scheme} (g : Y ⟶ Spec (.of (ResidueField R)))
local notation "f" => old ≫ s
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

include D in
/-- Every zero-abscissa input in the exact indexed smooth domain admits the actual transfer. -/
theorem residueTerminalPairOpen_zero_mem_of_indexedSmooth
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : (iso).hom (pullback.fst f g p) ∈ O)
    (hz : u ∈ (pullback.fst f g p).asIdeal) :
    p ∈ residueTerminalPairOpen hπ data j hj g :=
  residueTerminalPairOpen_zero_mem hπ data D j hj g hk0 hk p
    ((residueTerminalIndexedSource_smooth hπ data j hj _).mp hs) hz

include D in
/-- The puncture and actual boundary domain cover the entire indexed smooth first input. -/
theorem residueTerminalPairOpen_cover_of_indexedSmooth
    (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
    (p : (pullback f g : Scheme))
    (hs : (iso).hom (pullback.fst f g p) ∈ O) :
    u ∉ (pullback.fst f g p).asIdeal ∨ p ∈ residueTerminalPairOpen hπ data j hj g :=
  residueTerminalPairOpen_smooth_cover hπ data D j hj g hk0 hk p
    ((residueTerminalIndexedSource_smooth hπ data j hj _).mp hs)

end FLT.Mazur.WeierstrassDividedDepth
