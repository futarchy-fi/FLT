/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitTerminalRetainedTensorCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedAtlasIso
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedPositiveSplitAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitTerminalRetainedTensorCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedTensorDesc
import all FLT.Mazur.WeierstrassDividedPositiveSplitRetainedAtlasIso
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily

/-!
# Full terminal-neighbor compatibility on the original fixed atlas

The final retained chart transports from its proved whole tensor intersection.
This includes the smallest five-component cycle at positive start.
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
  (D : SplitNodeDepth W π depth) (hstart : 0 < start)
local notation "K" => ResidueField R

variable (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "j" => Fin.last s
local notation "i" => (Fin.mk (s - Fin.val j + 2) (by omega) : Fin (s + 1 + 3))
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "T" => terminalNodeChart hπ data D (s + 1) hs (by omega) (by omega) hp
local notation "V" => terminalNodeAtlasIso hπ data D (s + 1) hs (by omega) (by omega) hp
local notation "g" => globalSuccessiveTensorChart hπ data K s hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ index, ProjectiveLine.zero (ResidueField R) ≫ F index =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) index))
local notation "d" => positiveSplitCycleAtlasFamily hπ data D s hs hstart hk hp F w

/-- A positive last retained chart has its full terminal overlap at the original atlas indices. -/
theorem positiveSplitAtlasCompatible_terminal_neighbor :
    PositiveSplitAtlasCompatible hπ data D s hs hstart hk hp F w
      (Fin.succ 0) ⟨2, by omega⟩ := by
  have hi : i = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [← hi]
  apply pullback_compatible_of_source_isos V
    (positiveSplitRetainedAtlasIso hπ data s hs j)
    T g (m (Fin.succ 0)) (m i) (d (Fin.succ 0)) (d i) rfl
  · rw [terminalNodeAtlasIso_map]
  · rw [positiveSplitRetainedAtlasIso_global]
    apply (comp_eqToHom_heq _ _).trans
    exact (olderGlobalTensorChart_retention_heq hπ data s hs
      (s - s) 0 (by omega) hs (Nat.sub_self _)).trans
        (heq_of_eq (olderGlobalTensorChart_zero_retention hπ data s hs))
  · have H := positiveSplitCycleTerminalPositiveTensorDesc_compatible
      hπ data D s hs hstart hk hp F w
    simpa only [positiveSplitCycleRetainedTensorDesc, positiveSplitRetainedAtlasIso,
      Iso.trans_hom, asIso_hom, Category.assoc] using H


end FLT.Mazur.WeierstrassDividedDepth
