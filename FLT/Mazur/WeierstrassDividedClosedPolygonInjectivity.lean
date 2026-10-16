/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedRetainedIntersection
public import FLT.Mazur.WeierstrassDividedClosedRetainedTerminalIntersection

/-!
# Global injectivity on the complete original closed arithmetic stage

Every pair of original labels reflects equality in the polygon. Applying
this to the full original cover proves injectivity without removing any
source point, chart label, or corrected overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- Disjoint full chart images exclude every cross-chart point equality. -/
theorem fullChartDisjoint_points_ne {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hd : Disjoint (Set.range f) (Set.range g)) (x : X) (y : Y) : f x ≠ g y := by
  intro h
  exact Set.disjoint_left.mp hd ⟨x, rfl⟩ ⟨y, h.symm⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => arithmeticLabeledAtlasObject hπ data H 0 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu

/-- A single original chart introduces no additional point equality. -/
theorem arithmeticClosedSameLabel_points_eq (i : ArithmeticChartLabel (j + 1))
    (x y : A i) (h : G i x = G i y) : a i x = a i y :=
  congrArg (a i) ((G i).isOpenEmbedding.injective h)

/-- All ordered pairs of the complete original atlas reflect point equality. -/
theorem arithmeticClosedPolygonChart_points_eq (i k : ArithmeticChartLabel (j + 1))
    (x : A i) (y : A k) (h : G i x = G k y) : a i x = a k y := by
  cases i with
  | infinity =>
    cases k with
    | infinity => exact arithmeticClosedSameLabel_points_eq hπ data H j hj u hu _ x y h
    | initial b =>
      exact (arithmeticClosedInitialInfinity_points_eq hπ data H j hj u hu b y x h.symm).symm
    | retained idx b =>
      exact (fullChartDisjoint_points_ne _ _
        (arithmeticClosedInfinityRetained_disjoint hπ data H j hj u hu idx b) x y h).elim
    | terminal =>
      exact (fullChartDisjoint_points_ne _ _
        (arithmeticClosedInfinityTerminal_disjoint hπ data H j hj u hu) x y h).elim
  | initial b =>
    cases k with
    | infinity => exact arithmeticClosedInitialInfinity_points_eq hπ data H j hj u hu b x y h
    | initial e =>
      cases b <;> cases e
      · exact arithmeticClosedSameLabel_points_eq hπ data H j hj u hu _ x y h
      · exact arithmeticClosedInitialInitial_points_eq hπ data H j hj u hu x y h
      · exact (arithmeticClosedInitialInitial_points_eq hπ data H j hj u hu y x h.symm).symm
      · exact arithmeticClosedSameLabel_points_eq hπ data H j hj u hu _ x y h
    | retained idx e =>
      exact arithmeticClosedInitialRetained_points_eq hπ data H j hj u hu idx b e x y h
    | terminal =>
      exact (fullChartDisjoint_points_ne _ _
        (arithmeticClosedInitialTerminal_disjoint hπ data H j hj u hu b) x y h).elim
  | retained idx b =>
    cases k with
    | infinity =>
      exact (fullChartDisjoint_points_ne _ _
        (arithmeticClosedInfinityRetained_disjoint hπ data H j hj u hu idx b) y x h.symm).elim
    | initial e =>
      exact (arithmeticClosedInitialRetained_points_eq hπ data H j hj u hu idx e b y x
        h.symm).symm
    | retained other e =>
      exact arithmeticClosedRetained_points_eq hπ data H j hj u hu idx other b e x y h
    | terminal =>
      exact arithmeticClosedRetainedTerminal_points_eq hπ data H j hj u hu idx b x y h
  | terminal =>
    cases k with
    | infinity =>
      exact (fullChartDisjoint_points_ne _ _
        (arithmeticClosedInfinityTerminal_disjoint hπ data H j hj u hu) y x h.symm).elim
    | initial b =>
      exact (fullChartDisjoint_points_ne _ _
        (arithmeticClosedInitialTerminal_disjoint hπ data H j hj u hu b) y x h.symm).elim
    | retained idx b =>
      exact (arithmeticClosedRetainedTerminal_points_eq hπ data H j hj u hu idx b y x
        h.symm).symm
    | terminal => exact arithmeticClosedSameLabel_points_eq hπ data H j hj u hu _ x y h

/-- The actual complete closed polygon comparison is globally injective. -/
theorem arithmeticClosedPolygonMap_injective : Function.Injective F := by
  intro x y h
  obtain ⟨i, xi, rfl⟩ := arithmeticLabeledAtlas_cover hπ data H 0 (j + 1) hj x
  obtain ⟨k, yk, rfl⟩ := arithmeticLabeledAtlas_cover hπ data H 0 (j + 1) hj y
  have hx := congrArg (fun f ↦ f xi)
    (arithmeticClosedPolygonMap_chart hπ data H j hj u hu i)
  have hy := congrArg (fun f ↦ f yk)
    (arithmeticClosedPolygonMap_chart hπ data H j hj u hu k)
  exact arithmeticClosedPolygonChart_points_eq hπ data H j hj u hu i k xi yk
    (hx.symm.trans (h.trans hy))

end FLT.Mazur.WeierstrassDividedDepth
