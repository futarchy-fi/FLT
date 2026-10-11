/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLaurentRetainedIntersection
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasAdjacentReduction
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasAdjacentReduction

/-!
# Equality-cycle compatibility on the entire terminal-neighbor overlap

The Laurent chart and the last retained chart restrict to the same complete
terminal component on their original conic incidence open. Source isomorphisms
transport this equality to indices one and two of the fixed global atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "T" => terminalLaurentChart hπ data D (s + 1) hs (by omega) hk hp
local notation "V" => terminalLaurentAtlasIso hπ data D (s + 1) hs (by omega) hk hp
local notation "N" => olderSuccessiveTensorAtlasIso hπ data K s hs 0 hs
local notation "g" => globalSuccessiveTensorChart hπ data K s hs
local notation "J" => laurentConicComponentProjectiveIso D (start + s) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w

/-- The entire original terminal atlas intersection has equality of its two descended maps. -/
theorem zeroEqualityPositiveAtlasCompatible_terminal_neighbor :
    ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w
      (Fin.succ 0) ⟨2, by omega⟩ := by
  apply pullback_compatible_of_source_isos V N T g
    (m (Fin.succ 0)) (m ⟨2, by omega⟩) (d (Fin.succ 0)) (d ⟨2, by omega⟩) rfl
  · rw [terminalLaurentAtlasIso_map]
  · apply heq_of_eq
    exact (olderGlobalTensorChart_eq_index hπ data K s hs 0 hs).trans
      (olderGlobalTensorChart_zero_retention hπ data s hs)
  · have H := terminalLaurentPositiveRetained_compatible_of_conic
      hπ data D s hs hk hp (by omega)
      ((J).inv ≫ ProjectiveLine.endpointReversal K ≫ F ⟨s + 1, by omega⟩)
      (zeroEqualityCycleTerminalTensorDesc hπ data D s hs hk hp hpos F w)
      (zeroEqualityCycleTerminalTensorDesc_conic hπ data D s hs hk hp hpos F w)
    rw [← laurentConicComponentProjectiveIso_torus D (start + s) hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e)
      (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp] at H
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at H
    rw [zeroEqualityPositiveCycleAtlasFamily_terminal,
      zeroEqualityPositiveCycleAtlasFamily_terminal_retained,
      zeroEqualityCycleTerminalAtlasDesc_torus]
    exact H

/-- Only adjacent retained-chart equations remain for global equality-cycle descent. -/
theorem zeroEqualityPositiveAtlasCompatible_of_retained_adjacent
    (H : ∀ i j : Fin (s + 1 + 3), 2 ≤ i.val → j.val = i.val + 1 →
      j.val ≤ s + 2 →
      ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w i j) :
    ∀ i j, ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w i j := by
  apply zeroEqualityPositiveAtlasCompatible_of_adjacent hπ data D s hs hstart hk hp hpos F w
  intro i j hi hij hj
  by_cases hi1 : i.val = 1
  · have he : i = Fin.succ 0 := Fin.ext hi1
    have hn : j = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [he, hn]
    exact zeroEqualityPositiveAtlasCompatible_terminal_neighbor
      hπ data D s hs hstart hk hp hpos F w
  · exact H i j (by omega) hij hj

end FLT.Mazur.WeierstrassDividedDepth
