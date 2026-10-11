/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialInteriorCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTerminalCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorAtlasIso
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasInitialReduction
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialTerminalCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialInteriorCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasInitialReduction
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorAtlasIso
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility

/-!
# Complete compatibility of the positive-start equality-cycle atlas

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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "g" => globalInitialTensorChart hπ data K (1 + s) (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K 0 (by omega) s (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "V" => finiteInitialTensorAtlasIso hπ data K (s + 1) hs

/-- Numerical reindexing preserves the entire original initial tensor chart. -/
theorem globalInitialTensorChart_index_heq (a b : ℕ) (ha : a ≤ n) (hb : b ≤ n)
    (he : a = b) : HEq (globalInitialTensorChart hπ data K a ha)
      (globalInitialTensorChart hπ data K b hb) := by
  subst b
  rfl

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w

/-- The original initial chart agrees with its first retained neighbor on their full overlap. -/
theorem positiveEqualityAtlasCompatible_initial_neighbor :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w
      ⟨s + 3, by omega⟩ ⟨s + 2, by omega⟩ := by
  by_cases hs0 : 0 < s
  · let N := positiveEqualityInteriorAtlasIso hπ data s hs ⟨0, hs0⟩
    apply pullback_compatible_of_source_isos V N g gNext
      (m ⟨s + 3, by omega⟩) (m ⟨s + 2, by omega⟩)
      (d ⟨s + 3, by omega⟩) (d ⟨s + 2, by omega⟩)
      (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
    · have H := globalInitialTensorChart_eq_index hπ data K (s + 1) hs
      simp only [Fin.succ_mk] at H
      rw [H]
      exact globalInitialTensorChart_index_heq hπ data _ _ hs (by omega) (by omega)
    · have H := positiveEqualityInteriorAtlasIso_global hπ data s hs ⟨0, hs0⟩
      simp only [Fin.val_mk, Nat.sub_zero] at H
      rw [H]
      exact comp_eqToHom_heq _ _
    · rw [positiveEqualityCycleAtlasFamily_initial]
      have H := positiveEqualityInitialInteriorTensor_compatible
        hπ data D s hs hstart hk hp F w hs0
      simpa only [positiveEqualityInitialTensorDesc, positiveEqualityCycleInteriorTensorDesc,
        positiveEqualityInteriorAtlasIso, N, Iso.trans_hom, asIso_hom, Category.assoc,
        Nat.sub_zero] using H
  · have hs0' : s = 0 := by omega
    subst s
    let N := olderSuccessiveTensorAtlasIso hπ data K 0 hs 0 hs
    apply pullback_compatible_of_source_isos
      (finiteInitialTensorAtlasIso hπ data K 1 hs) N
      (globalInitialTensorChart hπ data K 1 hs)
      (olderGlobalTensorChart hπ data K 0 hs 0 hs)
      (globalTensorAtlasMap hπ data K 1 hs ⟨3, by omega⟩)
      (globalTensorAtlasMap hπ data K 1 hs ⟨2, by omega⟩) _ _ rfl
    · exact heq_of_eq (globalInitialTensorChart_eq_index hπ data K 1 hs)
    · exact heq_of_eq (olderGlobalTensorChart_eq_index hπ data K 0 hs 0 hs)
    · rw [positiveEqualityCycleAtlasFamily_initial,
        positiveEqualityCycleAtlasFamily_terminal_retained]
      exact positiveEqualityInitialTerminalTensor_compatible hπ data D hs hstart hk hp F w

/-- Every pair of original atlas charts has equality on its entire scheme intersection. -/
theorem positiveEqualityAtlasCompatible_all :
    ∀ i j, PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i j := by
  apply positiveEqualityAtlasCompatible_of_initial_neighbor hπ data D s hs hstart hk hp F w
  exact positiveEqualityAtlasCompatible_symm hπ data D s hs hstart hk hp F w
    (positiveEqualityAtlasCompatible_initial_neighbor hπ data D s hs hstart hk hp F w)

end FLT.Mazur.WeierstrassDividedDepth
