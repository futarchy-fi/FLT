/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedTerminalTensorCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorAtlasIso
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityRetainedTerminalTensorCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorAtlasIso
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasCompatibility

/-!
# Terminal retained equality-cycle compatibility on the fixed original atlas

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
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (t : ℕ) (hs : (t + 1) + 1 ≤ n)
local notation "s" => t + 1
local notation "K" => ResidueField R
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K t (by omega) 0 hs
local notation "gNext" => olderGlobalTensorChart hπ data K (t + 1) hs 0 hs
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "i" => (Fin.mk (s - t + 2) (by omega) : Fin (s + 1 + 3))
local notation "iNext" => (Fin.mk 2 (by omega) : Fin (s + 1 + 3))
local notation "e" => data (Fin.mk (t + 1) (by omega))

/-- The entire penultimate source isomorphism with its original tensor type exposed. -/
def positiveEqualityCyclePenultimateAtlasIso :
    Spec (.of (ScalarExtension W (π ^ (start + t)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ≅
        globalTensorAtlasObject hπ data K (s + 1) hs i :=
  positiveEqualityInteriorAtlasIso hπ data s hs ⟨t, by omega⟩
local notation "V" => positiveEqualityCyclePenultimateAtlasIso hπ data t hs
local notation "N" => olderSuccessiveTensorAtlasIso hπ data K s hs 0 hs

/-- The penultimate original source isomorphism preserves its whole global tensor map. -/
theorem positiveEqualityCyclePenultimateAtlasIso_global_heq :
    HEq ((V).hom ≫ m i) g := by
  rw [positiveEqualityCyclePenultimateAtlasIso, positiveEqualityInteriorAtlasIso_global]
  dsimp only [Fin.val_mk]
  apply (comp_eqToHom_heq _ _).trans
  exact (olderGlobalTensorChart_retention_heq hπ data t (by omega)
    (s - t) (0 + 1) (by omega) (by omega) (by omega)).trans
      (adjacentRetainedOldGlobalTensorChart_heq hπ data K
        t (by omega) 0 hs)

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hstart : 0 < start) (hk : 2 * (start + (t + 1) + 1) ≤ depth)
  (hp : 2 * (start + (t + 1) + 1) = depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * (t + 1) + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => positiveEqualityCycleAtlasFamily
  hπ data D s hs hstart hk hp F w

/-- The complete actual intersection of neighboring positive indexed charts is compatible. -/
theorem positiveEqualityAtlasCompatible_retained_terminal_neighbor :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i iNext := by
  apply pullback_compatible_of_source_isos V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · exact positiveEqualityCyclePenultimateAtlasIso_global_heq hπ data t hs
  · exact heq_of_eq (olderGlobalTensorChart_eq_index hπ data K s hs 0 hs)
  · rw [positiveEqualityCycleAtlasFamily_terminal_retained]
    have H := positiveEqualityCycleRetainedTerminalTensorDesc_compatible
      hπ data D t hs hstart hk hp F w
    simpa only [positiveEqualityCyclePenultimateAtlasIso,
      positiveEqualityCyclePenultimateTensorDesc,
      positiveEqualityCycleInteriorTensorDesc, positiveEqualityInteriorAtlasIso,
      Iso.trans_hom, asIso_hom,
      positiveEqualityCycleTerminalTensorDesc, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
