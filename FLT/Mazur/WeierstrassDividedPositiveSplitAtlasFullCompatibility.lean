/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialRetainedCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedAtlasIso
public import FLT.Mazur.WeierstrassDividedPositiveSplitAtlasInitialReduction
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFullCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitInitialRetainedCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasInitialReduction
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedAtlasIso
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasCompatibility

/-!
# Complete compatibility of the positive-start strict-cycle atlas

The compatibility on the entire tensor intersection transports through the
original source isomorphisms and numerical equality of the global stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open Limits

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "g" => globalInitialTensorChart hπ data K (1 + s) (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K 0 (by omega) s (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "V" => finiteInitialTensorAtlasIso hπ data K (s + 1) hs

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => positiveSplitCycleAtlasFamily hπ data D s hs hstart hk hp F w

/-- The original initial chart agrees with its first retained neighbor on their full overlap. -/
theorem positiveSplitAtlasCompatible_initial_neighbor :
    PositiveSplitAtlasCompatible hπ data D s hs hstart hk hp F w
      ⟨s + 3, by omega⟩ ⟨s + 2, by omega⟩ := by
  let N := positiveSplitRetainedAtlasIso hπ data s hs ⟨0, by omega⟩
  apply pullback_compatible_of_source_isos V N g gNext
    (m ⟨s + 3, by omega⟩) (m ⟨s + 2, by omega⟩)
    (d ⟨s + 3, by omega⟩) (d ⟨s + 2, by omega⟩)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · have H := globalInitialTensorChart_eq_index hπ data K (s + 1) hs
    simp only [Fin.succ_mk] at H
    rw [H]
    exact globalInitialTensorChart_index_heq hπ data _ _ hs (by omega) (by omega)
  · have H := positiveSplitRetainedAtlasIso_global hπ data s hs ⟨0, by omega⟩
    simp only [Fin.val_mk, Nat.sub_zero] at H
    rw [H]
    exact comp_eqToHom_heq _ _
  · rw [positiveSplitCycleAtlasFamily_initial]
    have H := positiveSplitInitialRetainedTensor_compatible
      hπ data D s hs hstart hk hp F w
    simpa only [positiveSplitInitialTensorDesc, positiveSplitCycleRetainedTensorDesc,
      positiveSplitRetainedAtlasIso, N, Iso.trans_hom, asIso_hom, Category.assoc,
      Nat.sub_zero] using H

/-- Every pair of original atlas charts has equality on its entire scheme intersection. -/
theorem positiveSplitAtlasCompatible_all :
    ∀ i j, PositiveSplitAtlasCompatible hπ data D s hs hstart hk hp F w i j := by
  apply positiveSplitAtlasCompatible_of_initial_neighbor hπ data D s hs hstart hk hp F w
  exact positiveSplitAtlasCompatible_symm hπ data D s hs hstart hk hp F w
    (positiveSplitAtlasCompatible_initial_neighbor hπ data D s hs hstart hk hp F w)

end FLT.Mazur.WeierstrassDividedDepth
