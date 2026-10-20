/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAtlasPairFormulaInput
public import FLT.Mazur.WeierstrassDividedFiniteSecantInput

/-!
# Actual older and terminal atlas coordinates for addition formulas

Contract the retained older chart to its preceding divided chart and contract
the terminal chart to the same depth. These maps preserve the original cubic
and coefficient morphisms at their exact indices in the complete atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (k : ℕ) (hk : k + 1 ≤ n) (s : ℕ) (hs : k + 1 + s ≤ n)
local notation "j" => k + 1 + s
local notation "a" => (Fin.succ ⟨s + 1, by omega⟩ : Fin (j + 3))
local notation "d" => data ⟨k, by omega⟩
local notation "e" => data ⟨k + 1, by omega⟩
local notation "base" => finiteGlobalStructure hπ data j hs

/-- Common divided coordinates on the entire retained older integral chart. -/
def olderAtlasFormulaCoordinates : globalIntegralAtlasObject data j hs a ⟶ chart d :=
  eqToHom (finiteOlderExteriorObject_eq data k hk s hs) ≫ xContraction hπ d e

/-- The older coordinate map retains the original cubic contraction. -/
@[reassoc] theorem olderAtlasFormulaCoordinates_cubic :
    olderAtlasFormulaCoordinates hπ data k hk s hs ≫ toCurve d =
      globalIntegralAtlasMap hπ data j hs a ≫ finiteGlobalContraction hπ data j hs := by
  apply (cancel_epi (eqToHom (finiteOlderExteriorObject_eq data k hk s hs).symm)).mp
  rw [globalIntegralAtlasMap_older_assoc hπ data k hk s hs]
  simp only [olderAtlasFormulaCoordinates, ← Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp]
  rw [olderGlobalChart, Category.assoc, finiteLocalChart_contraction,
    olderSuccessiveChart_toCurve]

/-- The actual older chart supplies the coefficient equality needed by pair formulas. -/
@[reassoc] theorem olderAtlasFormulaCoordinates_structure :
    olderAtlasFormulaCoordinates hπ data k hk s hs ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Coordinate W (π ^ (start + k)) (d).b3 (d).b4 (d).b6))) =
      globalIntegralAtlasMap hπ data j hs a ≫ base := by
  rw [← toCurve_structure d, ← Category.assoc, olderAtlasFormulaCoordinates_cubic,
    Category.assoc]
  rw [finiteGlobalStructure]

/-- The terminal integral atlas chart is the actual divided chart of the final stage. -/
theorem globalIntegralAtlasMap_terminal :
    globalIntegralAtlasMap hπ data j hs (1 : Fin (j + 3)) =
      finiteSecantDividedChart hπ data j hs := rfl

/-- Terminal coordinates at the same preceding depth as the retained older chart. -/
def terminalAtlasFormulaCoordinates :
    globalIntegralAtlasObject data j hs (1 : Fin (j + 3)) ⟶ chart d :=
  depthTransitionMorphism π (start + k) (start + j) hπ (by omega) W
    (d).b3 (d).b4 (d).b6 (data ⟨j, by omega⟩).b3
    (data ⟨j, by omega⟩).b4 (data ⟨j, by omega⟩).b6
    (d).factor3 (d).factor4 (d).factor6
    (data ⟨j, by omega⟩).factor3 (data ⟨j, by omega⟩).factor4 (data ⟨j, by omega⟩).factor6

/-- The terminal coordinate contraction preserves its exact original cubic input. -/
@[reassoc] theorem terminalAtlasFormulaCoordinates_cubic :
    terminalAtlasFormulaCoordinates hπ data k hk s hs ≫ toCurve d =
      globalIntegralAtlasMap hπ data j hs (1 : Fin (j + 3)) ≫
        finiteGlobalContraction hπ data j hs := by
  rw [globalIntegralAtlasMap_terminal, finiteSecantDividedChart_contraction]
  exact depthTransitionMorphism_contraction π (start + k) (start + j) hπ (by omega)
    W (d).b3 (d).b4 (d).b6 (data ⟨j, by omega⟩).b3
    (data ⟨j, by omega⟩).b4 (data ⟨j, by omega⟩).b6
    (d).factor3 (d).factor4 (d).factor6
    (data ⟨j, by omega⟩).factor3 (data ⟨j, by omega⟩).factor4 (data ⟨j, by omega⟩).factor6

/-- Both older and terminal coordinates have the same unchanged coefficient structure. -/
@[reassoc] theorem terminalAtlasFormulaCoordinates_structure :
    terminalAtlasFormulaCoordinates hπ data k hk s hs ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Coordinate W (π ^ (start + k)) (d).b3 (d).b4 (d).b6))) =
      globalIntegralAtlasMap hπ data j hs (1 : Fin (j + 3)) ≫ base := by
  rw [← toCurve_structure d, ← Category.assoc, terminalAtlasFormulaCoordinates_cubic,
    Category.assoc]
  rw [finiteGlobalStructure]

end FLT.Mazur.WeierstrassDividedDepth
