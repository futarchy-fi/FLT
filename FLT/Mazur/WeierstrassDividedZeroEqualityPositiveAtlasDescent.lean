/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityInteriorAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityRetainedTerminalAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityZeroInteriorAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityOneZeroTerminalAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility

import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityRetainedTerminalAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityZeroInteriorAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityOneZeroTerminalAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasCompatibility

/-!
# Complete original-atlas descent for every positive equality depth

Interior, terminal and initial retained neighbors exhaust the adjacent pairs.
Together with the exterior equations they glue the original finite atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "C" => ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w
local notation "K" => ResidueField R
local notation "U" => globalTensorOpenCover hπ data K (s + 1) hs
local notation "d" => zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w

/-- All adjacent retained charts agree on their entire actual intersections. -/
theorem zeroEqualityPositiveAtlasCompatible_retained_adjacent
    (i k : Fin (s + 1 + 3)) (hi : 2 ≤ i.val) (hik : k.val = i.val + 1)
    (hkbound : k.val ≤ s + 2) : C i k := by
  apply zeroEqualityPositiveAtlasCompatible_symm hπ data D s hs hstart hk hp hpos F w
  by_cases hsone : s = 1
  · subst s
    have hi' : i = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
    have hk' : k = ⟨3, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi', hk']
    exact zeroEqualityPositiveAtlasCompatible_one_zero_terminal hπ data D hs hstart hk hp F w
  have hs2 : 1 < s := by omega
  by_cases hklast : k.val = s + 2
  · have hi' : i = ⟨s + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    have hk' : k = ⟨s + 2, by omega⟩ := Fin.ext hklast
    rw [hi', hk']
    exact zeroEqualityPositiveAtlasCompatible_zero_interior hπ data D s hs hstart hk hp hs2 F w
  by_cases hi2 : i.val = 2
  · obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le (show 2 ≤ s by omega)
    have he : s = t + 2 := by omega
    clear ht
    subst s
    have hi' : i = ⟨2, by omega⟩ := Fin.ext hi2
    have hk' : k = ⟨t + 2 - t + 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi', hk']
    exact zeroEqualityPositiveAtlasCompatible_retained_terminal_neighbor
      hπ data t hs D hstart hk hp F w
  let j : Fin (s - 1) := ⟨s + 1 - k.val, by omega⟩
  have hj : j.val + 1 < s - 1 := by dsimp [j]; omega
  have H := zeroEqualityPositiveAtlasCompatible_interior_neighbors
    hπ data D s hs hstart hk hp hpos ⟨j.val, by omega⟩ hj F w
  have hi' : (⟨s - (j.val + 1) + 1, by omega⟩ : Fin (s + 1 + 3)) = i := by
    apply Fin.ext
    dsimp [j]
    omega
  have hk' : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) = k := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa only [hi', hk'] using H

/-- Every pair of original charts is compatible, including the depth-one terminal pair. -/
theorem zeroEqualityPositiveCycleAtlasFamily_compatible : ∀ i k, C i k :=
  zeroEqualityPositiveAtlasCompatible_of_retained_adjacent hπ data D s hs hstart hk hp hpos F w
    (zeroEqualityPositiveAtlasCompatible_retained_adjacent hπ data D s hs hstart hk hp hpos F w)

/-- The cyclic family descends to the entire original residue model at positive equality depth. -/
def zeroEqualityPositiveCycleGlobalDesc : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y :=
  (U).glueMorphisms d
    (zeroEqualityPositiveCycleAtlasFamily_compatible hπ data D s hs hstart hk hp hpos F w)

/-- Gluing recovers each complete original atlas chart. -/
@[reassoc] theorem zeroEqualityPositiveCycleGlobalDesc_atlas (i : Fin (s + 1 + 3)) :
    globalTensorAtlasMap hπ data K (s + 1) hs i ≫
      zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w = d i :=
  (U).ι_glueMorphisms d
    (zeroEqualityPositiveCycleAtlasFamily_compatible hπ data D s hs hstart hk hp hpos F w) i

/-- Full chart restrictions determine the global descent uniquely for arbitrary targets. -/
theorem zeroEqualityPositiveCycleGlobalDesc_unique
    (f : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (h : ∀ i, globalTensorAtlasMap hπ data K (s + 1) hs i ≫ f = d i) :
    f = zeroEqualityPositiveCycleGlobalDesc hπ data D s hs hstart hk hp hpos F w := by
  apply (U).hom_ext
  intro i
  exact (h i).trans
    (zeroEqualityPositiveCycleGlobalDesc_atlas hπ data D s hs hstart hk hp hpos F w i).symm

end FLT.Mazur.WeierstrassDividedDepth
