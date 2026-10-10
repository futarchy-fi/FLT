/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveDescent

/-!
# Constructed local maps from a compatible cyclic projective family

The endpoint relations of the complete family supply descent at every
positive-depth retained node, in both original tangent orders.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
/-- The cyclic endpoint relation supplies the first retained node's ordered compatibility. -/
theorem zeroSplitCycleFamily_first_compatible {K : Type u} [Field K]
    (s : ℕ) (j : Fin s) {Y : Scheme.{u}} (F : Fin (2 * s + 3) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.infinity K ≫ F ⟨j.val + 2, by omega⟩ =
      ProjectiveLine.zero K ≫ F ⟨j.val + 1, by omega⟩ := by
  have hn : PolygonPinching.next (by omega) (⟨j.val + 1, by omega⟩ : Fin (2 * s + 3)) =
      ⟨j.val + 2, by omega⟩ := by
    apply Fin.ext
    change (j.val + 1 + 1) % (2 * s + 3) = j.val + 2
    exact Nat.mod_eq_of_lt (by omega)
  simpa only [hn] using (w ⟨j.val + 1, by omega⟩).symm

/-- The same endpoint relation supplies the opposite node's unchanged cyclic direction. -/
theorem zeroSplitCycleFamily_second_compatible {K : Type u} [Field K]
    (s : ℕ) (j : Fin s) {Y : Scheme.{u}} (F : Fin (2 * s + 3) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.zero K ≫ F ⟨2 * s + 2 - (j.val + 1), by omega⟩ =
      ProjectiveLine.infinity K ≫ F ⟨2 * s + 2 - j.val, by omega⟩ := by
  have hn : PolygonPinching.next (by omega)
      (⟨2 * s + 2 - (j.val + 1), by omega⟩ : Fin (2 * s + 3)) =
      ⟨2 * s + 2 - j.val, by omega⟩ := by
    apply Fin.ext
    change (2 * s + 2 - (j.val + 1) + 1) % (2 * s + 3) = 2 * s + 2 - j.val
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  simpa only [hn] using w ⟨2 * s + 2 - (j.val + 1), by omega⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
  (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + (j.val + 1) + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D



variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The constructed arbitrary-target map on the entire first ordered original retained node. -/
def zeroSplitCycleFirstLocalDesc : Spec (.of (MiddleNodeOpen c)) ⟶ Y :=
  (zeroSplitCycle_positive_first_exists_unique_desc data D s hs hstart hp j
    (F ⟨j.val + 2, by omega⟩) (F ⟨j.val + 1, by omega⟩)
    (zeroSplitCycleFamily_first_compatible s j F w)).choose

/-- The first local map restricts to the right chart of the next cyclic component. -/
@[reassoc] theorem zeroSplitCycleFirstLocalDesc_conic :
    middleNodeFirstBranch c hc ≫ zeroSplitCycleFirstLocalDesc data D s hs hstart hp j F w =
      ProjectiveLine.right K ≫ F ⟨j.val + 2, by omega⟩ :=
  (zeroSplitCycle_positive_first_exists_unique_desc data D s hs hstart hp j
    (F ⟨j.val + 2, by omega⟩) (F ⟨j.val + 1, by omega⟩)
    (zeroSplitCycleFamily_first_compatible s j F w)).choose_spec.1.1

/-- The horizontal restriction retains the original reciprocal tangent scaling. -/
@[reassoc] theorem zeroSplitCycleFirstLocalDesc_line :
    ProjectiveLine.chartScaling K (tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫
        zeroSplitCycleFirstLocalDesc data D s hs hstart hp j F w =
      ProjectiveLine.left K ≫ F ⟨j.val + 1, by omega⟩ :=
  (zeroSplitCycle_positive_first_exists_unique_desc data D s hs hstart hp j
    (F ⟨j.val + 2, by omega⟩) (F ⟨j.val + 1, by omega⟩)
    (zeroSplitCycleFamily_first_compatible s j F w)).choose_spec.1.2

/-- The constructed arbitrary-target map on the full opposite ordered retained node. -/
def zeroSplitCycleSecondLocalDesc : Spec (.of (MiddleNodeOpen c)) ⟶ Y :=
  (zeroSplitCycle_positive_second_exists_unique_desc data D s hs hstart hp j
    (F ⟨2 * s + 2 - (j.val + 1), by omega⟩) (F ⟨2 * s + 2 - j.val, by omega⟩)
    (zeroSplitCycleFamily_second_compatible s j F w)).choose

/-- The opposite conic restriction keeps its actual negative original coordinate. -/
@[reassoc] theorem zeroSplitCycleSecondLocalDesc_conic :
    middleNodeFirstBranch c hc ≫ zeroSplitCycleSecondLocalDesc data D s hs hstart hp j F w =
      Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) ≫
        ProjectiveLine.left K ≫ F ⟨2 * s + 2 - (j.val + 1), by omega⟩ :=
  (zeroSplitCycle_positive_second_exists_unique_desc data D s hs hstart hp j
    (F ⟨2 * s + 2 - (j.val + 1), by omega⟩) (F ⟨2 * s + 2 - j.val, by omega⟩)
    (zeroSplitCycleFamily_second_compatible s j F w)).choose_spec.1.1

/-- The opposite horizontal restriction keeps its negatively scaled reciprocal coordinate. -/
@[reassoc] theorem zeroSplitCycleSecondLocalDesc_line :
    ProjectiveLine.chartScaling K (-tangent)⁻¹ ≫ middleNodeSecondBranch c hc ≫
        zeroSplitCycleSecondLocalDesc data D s hs hstart hp j F w =
      ProjectiveLine.right K ≫ F ⟨2 * s + 2 - j.val, by omega⟩ :=
  (zeroSplitCycle_positive_second_exists_unique_desc data D s hs hstart hp j
    (F ⟨2 * s + 2 - (j.val + 1), by omega⟩) (F ⟨2 * s + 2 - j.val, by omega⟩)
    (zeroSplitCycleFamily_second_compatible s j F w)).choose_spec.1.2

end FLT.Mazur.WeierstrassDividedDepth
