/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasBranches
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveAtlasBranches
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Proven branch overlap equations for adjacent positive cyclic charts

Each shared component's actual projective-chart fiber product maps to the
original atlas fiber product. Both ordered restrictions of the cyclic
family agree there as scheme morphisms, retaining the opposite sign.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The opposite component chart retains the original negative affine parameter. -/
irreducible_def zeroSplitCycleOppositeChart (K : Type u) [Field K] :
    ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫ ProjectiveLine.left K

/-- Composition exposes only the signed chart formula, keeping its pullbacks sealed. -/
theorem zeroSplitCycleOppositeChart_comp (K : Type u) [Field K]
    {Y : Scheme.{u}} (f : ProjectiveLine.scheme K ⟶ Y) :
    zeroSplitCycleOppositeChart K ≫ f =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ f := by
  rw [zeroSplitCycleOppositeChart_def, Category.assoc]

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth) (j : Fin s) (hj : j.val + 1 < s)
local notation "K" => ResidueField R
local notation "k" => (Fin.mk (j.val + 1) hj)
local notation "oldIndex" => (Fin.mk (s - j.val + 1) (by omega) : Fin (s + 1 + 3))
local notation "nextIndex" => (Fin.mk (s - (j.val + 1) + 1) (by omega) : Fin (s + 1 + 3))
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

section First
local notation "a" => ProjectiveLine.right K
local notation "b" => ProjectiveLine.left K
local notation "oldBranch" => zeroSplitCyclePositiveAtlasFirstConic
  hπ data D s hs hstart hp j
local notation "nextBranch" => zeroSplitCyclePositiveAtlasFirstLine
  hπ data D s hs hstart hp k

/-- The shared first component charts commute in the actual global model. -/
theorem zeroSplitCyclePositiveFirstOverlap_comm :
    (pullback.fst a b ≫ oldBranch) ≫ m oldIndex =
      (pullback.snd a b ≫ nextBranch) ≫ m nextIndex := by
  simp only [Category.assoc, zeroSplitCyclePositiveAtlasFirstConic_global,
    zeroSplitCyclePositiveAtlasFirstLine_global]
  exact pullback.condition_assoc (f := a) (g := b) ((Z ⟨j.val + 2, by omega⟩).left)

/-- The original first branch intersection maps into the complete atlas intersection. -/
def zeroSplitCyclePositiveFirstOverlap : pullback a b ⟶
    pullback (m oldIndex) (m nextIndex) :=
  pullback.lift (pullback.fst a b ≫ oldBranch) (pullback.snd a b ≫ nextBranch)
    (zeroSplitCyclePositiveFirstOverlap_comm hπ data D s hs hstart hp j hj)

/-- The comparison preserves the original conic projection. -/
@[reassoc] theorem zeroSplitCyclePositiveFirstOverlap_old :
    zeroSplitCyclePositiveFirstOverlap hπ data D s hs hstart hp j hj ≫
      pullback.fst (m oldIndex) (m nextIndex) = pullback.fst a b ≫ oldBranch :=
  pullback.lift_fst _ _ _

/-- The comparison preserves the original next horizontal projection. -/
@[reassoc] theorem zeroSplitCyclePositiveFirstOverlap_next :
    zeroSplitCyclePositiveFirstOverlap hπ data D s hs hstart hp j hj ≫
      pullback.snd (m oldIndex) (m nextIndex) = pullback.snd a b ≫ nextBranch :=
  pullback.lift_snd _ _ _

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w

/-- The original atlas descents agree on the complete shared first component overlap. -/
theorem zeroSplitCyclePositiveFirstOverlap_desc :
    zeroSplitCyclePositiveFirstOverlap hπ data D s hs hstart hp j hj ≫
        pullback.fst (m oldIndex) (m nextIndex) ≫ d oldIndex =
      zeroSplitCyclePositiveFirstOverlap hπ data D s hs hstart hp j hj ≫
        pullback.snd (m oldIndex) (m nextIndex) ≫ d nextIndex := by
  rw [zeroSplitCyclePositiveFirstOverlap_old_assoc,
    zeroSplitCyclePositiveFirstOverlap_next_assoc]
  simp only [zeroSplitCyclePositiveAtlasFirstConic_desc,
    zeroSplitCyclePositiveAtlasFirstLine_desc]
  exact pullback.condition_assoc (f := a) (g := b) (F ⟨j.val + 2, by omega⟩)

end First

section Second
local notation "a" => zeroSplitCycleOppositeChart K
local notation "b" => ProjectiveLine.right K
local notation "oldBranch" => zeroSplitCyclePositiveAtlasSecondConic
  hπ data D s hs hstart hp j
local notation "nextBranch" => zeroSplitCyclePositiveAtlasSecondLine
  hπ data D s hs hstart hp k

/-- The shared second component charts commute in the actual global model. -/
theorem zeroSplitCyclePositiveSecondOverlap_comm :
    (pullback.fst a b ≫ oldBranch) ≫ m oldIndex =
      (pullback.snd a b ≫ nextBranch) ≫ m nextIndex := by
  simp only [Category.assoc, zeroSplitCyclePositiveAtlasSecondConic_global,
    zeroSplitCyclePositiveAtlasSecondLine_global]
  rw [← zeroSplitCycleOppositeChart_comp]
  exact pullback.condition_assoc (f := a) (g := b) ((Z ⟨2 * s + 2 - (j.val + 1), by omega⟩).left)

/-- The original second branch intersection maps into the complete atlas intersection. -/
def zeroSplitCyclePositiveSecondOverlap : pullback a b ⟶
    pullback (m oldIndex) (m nextIndex) :=
  pullback.lift (pullback.fst a b ≫ oldBranch) (pullback.snd a b ≫ nextBranch)
    (zeroSplitCyclePositiveSecondOverlap_comm hπ data D s hs hstart hp j hj)

/-- The comparison preserves the original conic projection. -/
@[reassoc] theorem zeroSplitCyclePositiveSecondOverlap_old :
    zeroSplitCyclePositiveSecondOverlap hπ data D s hs hstart hp j hj ≫
      pullback.fst (m oldIndex) (m nextIndex) = pullback.fst a b ≫ oldBranch :=
  pullback.lift_fst _ _ _

/-- The comparison preserves the original next horizontal projection. -/
@[reassoc] theorem zeroSplitCyclePositiveSecondOverlap_next :
    zeroSplitCyclePositiveSecondOverlap hπ data D s hs hstart hp j hj ≫
      pullback.snd (m oldIndex) (m nextIndex) = pullback.snd a b ≫ nextBranch :=
  pullback.lift_snd _ _ _

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w

/-- The original atlas descents agree on the complete shared second component overlap. -/
theorem zeroSplitCyclePositiveSecondOverlap_desc :
    zeroSplitCyclePositiveSecondOverlap hπ data D s hs hstart hp j hj ≫
        pullback.fst (m oldIndex) (m nextIndex) ≫ d oldIndex =
      zeroSplitCyclePositiveSecondOverlap hπ data D s hs hstart hp j hj ≫
        pullback.snd (m oldIndex) (m nextIndex) ≫ d nextIndex := by
  rw [zeroSplitCyclePositiveSecondOverlap_old_assoc,
    zeroSplitCyclePositiveSecondOverlap_next_assoc]
  simp only [zeroSplitCyclePositiveAtlasSecondConic_desc,
    zeroSplitCyclePositiveAtlasSecondLine_desc]
  rw [← zeroSplitCycleOppositeChart_comp]
  exact pullback.condition_assoc (f := a) (g := b) (F ⟨2 * s + 2 - (j.val + 1), by omega⟩)

end Second

end FLT.Mazur.WeierstrassDividedDepth
