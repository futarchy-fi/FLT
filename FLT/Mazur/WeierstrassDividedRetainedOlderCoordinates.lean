/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderAtlasFormulaCoordinates

/-!
# Common lower-depth coordinates on any retained older chart

Index an older chart by its creation depth in an arbitrary final stage.
Contract its entire integral chart to any earlier divided depth, keeping
both its original cubic contraction and its coefficient morphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (l : ℕ) (hl : l < j)

/-- The chart created at depth l+1 has global index j-l+1 at stage j. -/
def retainedOlderFormulaIndex : Fin (j + 3) := ⟨j - l + 1, by clear * - j l hl; omega⟩

attribute [local irreducible] retainedOlderFormulaIndex

local notation "idx" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨l, by omega⟩
local notation "e" => data ⟨l + 1, by omega⟩

omit [IsDomain R] [IsBezout R] in
/-- The retained chart is the entire successive X equation scheme. -/
theorem retainedOlderFormulaObject_eq :
    globalIntegralAtlasObject data j hj idx = stepX e := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hl)
  have hi : retainedOlderFormulaIndex (l + 1 + s) l hl =
      (Fin.succ ⟨s + 1, by omega⟩ : Fin (l + 1 + s + 3)) := by
    apply Fin.ext
    unfold retainedOlderFormulaIndex
    dsimp only [Fin.val_mk, Fin.val_succ]
    omega
  rw [hi]
  exact finiteOlderExteriorObject_eq data l (by omega) s hj

/-- Coordinates at the depth immediately preceding this older chart's creation. -/
def retainedOlderFormulaCoordinates :
    globalIntegralAtlasObject data j hj idx ⟶ chart d :=
  eqToHom (retainedOlderFormulaObject_eq data j hj l hl) ≫ xContraction hπ d e

/-- The retained chart's original cubic contraction is independent of its later retention. -/
@[reassoc] theorem retainedOlderFormulaCoordinates_cubic :
    retainedOlderFormulaCoordinates hπ data j hj l hl ≫ toCurve d =
      globalIntegralAtlasMap hπ data j hj idx ≫ finiteGlobalContraction hπ data j hj := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hl)
  have hi : retainedOlderFormulaIndex (l + 1 + s) l hl =
      (Fin.succ ⟨s + 1, by omega⟩ : Fin (l + 1 + s + 3)) := by
    apply Fin.ext
    unfold retainedOlderFormulaIndex
    dsimp only [Fin.val_mk, Fin.val_succ]
    omega
  unfold retainedOlderFormulaCoordinates
  generalize_proofs hd he ho
  revert ho
  rw [hi]
  intro ho
  exact olderAtlasFormulaCoordinates_cubic hπ data l (by omega) s hj

variable (k : ℕ) (hkl : k ≤ l)
local notation "c" => data ⟨k, by omega⟩

/-- Coordinates on the whole retained chart at any common earlier depth. -/
def retainedOlderLowerCoordinates : globalIntegralAtlasObject data j hj idx ⟶ chart c :=
  retainedOlderFormulaCoordinates hπ data j hj l hl ≫
    depthTransitionMorphism π (start + k) (start + l) hπ (by omega) W
      (c).b3 (c).b4 (c).b6 (d).b3 (d).b4 (d).b6
      (c).factor3 (c).factor4 (c).factor6 (d).factor3 (d).factor4 (d).factor6

/-- Lowering depth preserves the exact original cubic input of the retained chart. -/
@[reassoc] theorem retainedOlderLowerCoordinates_cubic :
    retainedOlderLowerCoordinates hπ data j hj l hl k hkl ≫ toCurve c =
      globalIntegralAtlasMap hπ data j hj idx ≫ finiteGlobalContraction hπ data j hj := by
  rw [retainedOlderLowerCoordinates, Category.assoc]
  dsimp only [toCurve]
  rw [
    depthTransitionMorphism_contraction π (start + k) (start + l) hπ (by omega) W
      (c).b3 (c).b4 (c).b6 (d).b3 (d).b4 (d).b6
      (c).factor3 (c).factor4 (c).factor6 (d).factor3 (d).factor4 (d).factor6]
  exact retainedOlderFormulaCoordinates_cubic hπ data j hj l hl

/-- The common lower-depth coordinates preserve the actual base point. -/
@[reassoc] theorem retainedOlderLowerCoordinates_structure :
    retainedOlderLowerCoordinates hπ data j hj l hl k hkl ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Coordinate W (π ^ (start + k)) (c).b3 (c).b4 (c).b6))) =
      globalIntegralAtlasMap hπ data j hj idx ≫ finiteGlobalStructure hπ data j hj := by
  rw [← toCurve_structure c, ← Category.assoc, retainedOlderLowerCoordinates_cubic,
    Category.assoc]
  rw [finiteGlobalStructure]

end FLT.Mazur.WeierstrassDividedDepth
