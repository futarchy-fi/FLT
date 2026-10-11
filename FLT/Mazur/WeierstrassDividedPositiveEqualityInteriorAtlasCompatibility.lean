/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorAtlasIso
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorAtlasIso
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility

/-!
# Full adjacent interior equality-cycle compatibility at the fixed original atlas indices

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
  (hp : 2 * (start + s + 1) = depth) (j : Fin s)
local notation "K" => ResidueField R
variable (hj : j.val + 1 < s)
local notation "nextJ" => (Fin.mk (j.val + 1) (by omega) : Fin s)
local notation "r" => s - (j.val + 1)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K
  j.val (by omega) r (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K
  (j.val + 1) (by omega) r (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "i" => (Fin.mk (s - j.val + 2) (by omega) : Fin (s + 1 + 3))
local notation "iNext" => (Fin.mk (s - (j.val + 1) + 2) (by omega) : Fin (s + 1 + 3))
local notation "V" => positiveEqualityInteriorAtlasIso hπ data s hs j
local notation "N" => positiveEqualityInteriorAtlasIso hπ data s hs nextJ

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w

include hj in
/-- The complete actual intersection of neighboring positive indexed charts is compatible. -/
theorem positiveEqualityAtlasCompatible_interior_neighbors :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i iNext := by
  apply pullback_compatible_of_source_isos
    (X := finiteGlobalTensorModel hπ data K (j.val + 2 + r) (by omega))
    V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · rw [positiveEqualityInteriorAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data j.val (by omega)
      (s - j.val) (r + 1) (by omega) (by omega) (by omega)).trans
        (adjacentRetainedOldGlobalTensorChart_heq hπ data K
          j.val (by omega) r (by omega))
  · rw [positiveEqualityInteriorAtlasIso_global]
    exact comp_eqToHom_heq _ _
  · have H := positiveEqualityCycleInteriorTensorDesc_compatible
      hπ data D s hs hstart hk hp ⟨j.val, by omega⟩ hj r (by dsimp; omega) F w
    simpa only [positiveEqualityCycleInteriorTensorDesc, positiveEqualityInteriorAtlasIso,
      Iso.trans_hom, asIso_hom, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
