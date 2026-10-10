/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Full adjacent positive compatibility at the fixed original atlas indices

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

/-- Source isomorphisms and an equal target preserve full pullback compatibility. -/
theorem pullback_compatible_of_source_isos {A B X A' B' X' Y : Scheme.{u}}
    (v : A ≅ A') (z : B ≅ B') (g : A ⟶ X) (h : B ⟶ X)
    (g' : A' ⟶ X') (h' : B' ⟶ X') (f : A' ⟶ Y) (k : B' ⟶ Y)
    (he : X' = X) (hv : HEq (v.hom ≫ g') g) (hz : HEq (z.hom ≫ h') h)
    (H : pullback.fst g h ≫ v.hom ≫ f = pullback.snd g h ≫ z.hom ≫ k) :
    pullback.fst g' h' ≫ f = pullback.snd g' h' ≫ k := by
  subst X'
  have hv' := eq_of_heq hv
  have hz' := eq_of_heq hz
  let a := pullback.fst g' h' ≫ v.inv
  let b := pullback.snd g' h' ≫ z.inv
  have hab : a ≫ g = b ≫ h := by
    rw [← hv', ← hz']
    simp only [a, b, Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.condition
  have hh := congrArg (fun morphism => pullback.lift a b hab ≫ morphism) H
  simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    a, b, Iso.inv_hom_id_assoc] using hh

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (j : Fin s)
/-- Reindexing the number of retained stages preserves the entire original tensor map. -/
theorem olderGlobalTensorChart_retention_heq (k : ℕ) (hk : k + 1 ≤ n)
    (a b : ℕ) (ha : k + 1 + a ≤ n) (hb : k + 1 + b ≤ n) (he : a = b) :
    HEq (olderGlobalTensorChart hπ data (ResidueField R) k hk a ha)
      (olderGlobalTensorChart hπ data (ResidueField R) k hk b hb) := by
  subst b
  rfl

local notation "K" => ResidueField R
variable (hj : j.val + 1 < s)
local notation "nextJ" => (Fin.mk (j.val + 1) hj : Fin s)
local notation "r" => s - (j.val + 2)
local notation "g" => adjacentRetainedOldGlobalTensorChart hπ data K
  (j.val + 1) (by omega) r (by omega)
local notation "gNext" => olderGlobalTensorChart hπ data K
  ((j.val + 1) + 1) (by omega) r (by omega)
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "i" => (Fin.mk (s - j.val + 1) (by omega) : Fin (s + 1 + 3))
local notation "iNext" => (Fin.mk (s - (j.val + 1) + 1) (by omega) : Fin (s + 1 + 3))
local notation "V" => zeroSplitCyclePositiveAtlasIso hπ data s hs j
local notation "N" => zeroSplitCyclePositiveAtlasIso hπ data s hs nextJ

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w

/-- The complete actual intersection of neighboring positive indexed charts is compatible. -/
theorem zeroSplitCycleAtlasCompatible_positive_neighbors :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i iNext := by
  apply pullback_compatible_of_source_isos V N g gNext (m i) (m iNext) (d i) (d iNext)
    (finiteGlobalTensorModel_index_congr hπ data K hs (by omega) (by omega))
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data (j.val + 1) (by omega)
      (s - (j.val + 1)) (r + 1) (by omega) (by omega) (by omega)).trans
        (adjacentRetainedOldGlobalTensorChart_heq hπ data K
          (j.val + 1) (by omega) r (by omega))
  · rw [zeroSplitCyclePositiveAtlasIso_global]
    exact comp_eqToHom_heq _ _
  · exact zeroSplitCyclePositiveTensorDesc_compatible
      hπ data D s hs hstart hp j hj r (by omega) F w

end FLT.Mazur.WeierstrassDividedDepth
