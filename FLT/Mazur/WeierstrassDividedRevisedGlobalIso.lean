/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedSeparation
public import FLT.Mazur.WeierstrassDividedRevisedTerminalReflection

/-!
# Global injectivity on the complete original first-order arithmetic stage

Every pair of original labels reflects equality in the polygon. Applying
this to the full original cover proves injectivity without removing any
source point, chart label, or corrected overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFirstOriginalRevisedChart arithmeticRevisedPolygon

/-- Disjoint full chart images exclude every cross-chart point equality. -/
theorem revisedDisjoint_points_ne {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hd : Disjoint (Set.range f) (Set.range g)) (x : X) (y : Y) : f x ≠ g y := by
  intro h
  exact Set.disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, h.symm⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => arithmeticLabeledAtlasObject hπ data H 1 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "F" => arithmeticFirstOriginalRevisedGlobalMap hπ data H j hj u hu

/-- A single original chart introduces no additional point equality. -/
theorem arithmeticFirstRevisedSameLabel_points_eq (i : ArithmeticChartLabel (j + 1))
    (x y : A i) (h : G i x = G i y) : a i x = a i y :=
  congrArg (a i) ((G i).isOpenEmbedding.injective h)

/-- All ordered pairs of the complete original atlas reflect point equality. -/
theorem arithmeticFirstRevisedPolygonChart_points_eq (i k : ArithmeticChartLabel (j + 1))
    (x : A i) (y : A k) (h : G i x = G k y) : a i x = a k y := by
  cases i with
  | infinity =>
    cases k with
    | infinity => exact arithmeticFirstRevisedSameLabel_points_eq hπ data H j hj u hu _ x y h
    | initial b =>
      exact (arithmeticFirstRevisedInitialInfinity_points_eq hπ data H j hj u hu b y x h.symm).symm
    | retained idx b =>
      exact (revisedDisjoint_points_ne _ _
        (arithmeticFirstRevisedInfinityRetained_disjoint hπ data H j hj u hu idx b) x y h).elim
    | terminal =>
      exact (revisedDisjoint_points_ne _ _
        (arithmeticFirstRevisedInfinityTerminal_disjoint hπ data H j hj u hu) x y h).elim
  | initial b =>
    cases k with
    | infinity => exact arithmeticFirstRevisedInitialInfinity_points_eq hπ data H j hj u hu b x y h
    | initial e =>
      cases b <;> cases e
      · exact arithmeticFirstRevisedSameLabel_points_eq hπ data H j hj u hu _ x y h
      · exact arithmeticFirstRevisedInitialInitial_points_eq hπ data H j hj u hu x y h
      · exact (arithmeticFirstRevisedInitialInitial_points_eq hπ data H j hj u hu y x h.symm).symm
      · exact arithmeticFirstRevisedSameLabel_points_eq hπ data H j hj u hu _ x y h
    | retained idx e =>
      exact arithmeticFirstRevisedInitialRetained_points_eq hπ data H j hj u hu idx b e x y h
    | terminal =>
      exact (revisedDisjoint_points_ne _ _
        (arithmeticFirstRevisedInitialTerminal_disjoint hπ data H j hj u hu b) x y h).elim
  | retained idx b =>
    cases k with
    | infinity =>
      exact (revisedDisjoint_points_ne _ _
        (arithmeticFirstRevisedInfinityRetained_disjoint hπ data H j hj u hu idx b) y x h.symm).elim
    | initial e =>
      exact (arithmeticFirstRevisedInitialRetained_points_eq hπ data H j hj u hu idx e b y x
        h.symm).symm
    | retained other e =>
      exact arithmeticFirstRevisedRetained_points_eq hπ data H j hj u hu idx other b e x y h
    | terminal =>
      exact arithmeticFirstRevisedRetainedTerminal_points_eq hπ data H j hj u hu idx b x y h
  | terminal =>
    cases k with
    | infinity =>
      exact (revisedDisjoint_points_ne _ _
        (arithmeticFirstRevisedInfinityTerminal_disjoint hπ data H j hj u hu) y x h.symm).elim
    | initial b =>
      exact (revisedDisjoint_points_ne _ _
        (arithmeticFirstRevisedInitialTerminal_disjoint hπ data H j hj u hu b) y x h.symm).elim
    | retained idx b =>
      exact (arithmeticFirstRevisedRetainedTerminal_points_eq hπ data H j hj u hu idx b y x
        h.symm).symm
    | terminal => exact arithmeticFirstRevisedSameLabel_points_eq hπ data H j hj u hu _ x y h

/-- The actual complete first-order revised comparison is globally injective. -/
theorem arithmeticFirstOriginalRevisedGlobalMap_injective : Function.Injective F := by
  intro x y h
  obtain ⟨i, xi, rfl⟩ := arithmeticLabeledAtlas_cover hπ data H 1 (j + 1) hj x
  obtain ⟨k, yk, rfl⟩ := arithmeticLabeledAtlas_cover hπ data H 1 (j + 1) hj y
  have hx := congrArg (fun f ↦ f xi)
    (arithmeticFirstOriginalRevisedGlobalMap_chart hπ data H j hj u hu i)
  have hy := congrArg (fun f ↦ f yk)
    (arithmeticFirstOriginalRevisedGlobalMap_chart hπ data H j hj u hu k)
  exact arithmeticFirstRevisedPolygonChart_points_eq hπ data H j hj u hu i k xi yk
    (hx.symm.trans (h.trans hy))

/-- The full original first-order stage is isomorphic to the independent revised polygon. -/
instance arithmeticFirstOriginalRevisedGlobalMap_isIso : IsIso F :=
  arithmeticFirstOriginalRevisedGlobalMap_isIso_of_injective hπ data H j hj u hu
    (arithmeticFirstOriginalRevisedGlobalMap_injective hπ data H j hj u hu)

/-- The complete first-order comparison retains all original charts and points. -/
def arithmeticFirstOriginalRevisedGlobalIso :
    finiteGlobalArithmeticStage hπ data (j + 1) hj 1 ≅
      arithmeticRevisedPolygon data H 1 j hj u hu := asIso F

end FLT.Mazur.WeierstrassDividedDepth
