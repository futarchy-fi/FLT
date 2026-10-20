/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSmoothAdvance

/-!
# Promote smooth points to a supplied common finite stage

Reindex the actual sequence of unchanged-open embeddings by its source and
target stages. No finite models are identified: the comparison is an open
immersion preserving the original cubic map and coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

/-- Reindex an iterated promotion by an equal numerical target, retaining its actual scheme. -/
def finiteGlobalSmoothAdvanceTo (i l j : ℕ) (he : i + l = j) (hj : j ≤ n) :
    (finiteGlobalStructure hπ data i (by omega)).smoothLocus.toScheme ⟶
      (finiteGlobalStructure hπ data j hj).smoothLocus.toScheme := by
  subst j
  exact finiteGlobalSmoothAdvance hπ data i l hj

instance finiteGlobalSmoothAdvanceTo_open (i l j : ℕ) (he : i + l = j) (hj : j ≤ n) :
    IsOpenImmersion (finiteGlobalSmoothAdvanceTo hπ data i l j he hj) := by
  subst j
  unfold finiteGlobalSmoothAdvanceTo
  infer_instance

/-- Numerical target reindexing preserves the original cubic contraction. -/
@[reassoc] theorem finiteGlobalSmoothAdvanceTo_contraction
    (i l j : ℕ) (he : i + l = j) (hj : j ≤ n) :
    finiteGlobalSmoothAdvanceTo hπ data i l j he hj ≫
        (finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫
          finiteGlobalContraction hπ data j hj =
      (finiteGlobalStructure hπ data i (by omega)).smoothLocus.ι ≫
        finiteGlobalContraction hπ data i (by omega) := by
  subst j
  exact finiteGlobalSmoothAdvance_contraction hπ data i l hj

/-- Numerical target reindexing preserves the original coefficient structure. -/
@[reassoc] theorem finiteGlobalSmoothAdvanceTo_structure
    (i l j : ℕ) (he : i + l = j) (hj : j ≤ n) :
    finiteGlobalSmoothAdvanceTo hπ data i l j he hj ≫
        (finiteGlobalStructure hπ data j hj).smoothLocus.ι ≫
          finiteGlobalStructure hπ data j hj =
      (finiteGlobalStructure hπ data i (by omega)).smoothLocus.ι ≫
        finiteGlobalStructure hπ data i (by omega) := by
  subst j
  exact finiteGlobalSmoothAdvance_structure hπ data i l hj

variable (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data i (hij.trans hj)
local notation "next" => finiteGlobalStructure hπ data j hj

/-- The actual promotion from the source-stage smooth model to the supplied target stage. -/
def finiteGlobalSmoothTransition : (base).smoothLocus.toScheme ⟶
    (next).smoothLocus.toScheme :=
  finiteGlobalSmoothAdvanceTo hπ data i (j - i) j (Nat.add_sub_of_le hij) hj

instance finiteGlobalSmoothTransition_open :
    IsOpenImmersion (finiteGlobalSmoothTransition hπ data i j hij hj) := by
  unfold finiteGlobalSmoothTransition
  infer_instance

/-- Promotion preserves the entire original cubic contraction. -/
@[reassoc] theorem finiteGlobalSmoothTransition_contraction :
    finiteGlobalSmoothTransition hπ data i j hij hj ≫ (next).smoothLocus.ι ≫
        finiteGlobalContraction hπ data j hj =
      (base).smoothLocus.ι ≫ finiteGlobalContraction hπ data i (hij.trans hj) :=
  finiteGlobalSmoothAdvanceTo_contraction hπ data i (j - i) j (Nat.add_sub_of_le hij) hj

/-- Promotion retains the original coefficient structure on the entire smooth source. -/
@[reassoc] theorem finiteGlobalSmoothTransition_structure :
    finiteGlobalSmoothTransition hπ data i j hij hj ≫ (next).smoothLocus.ι ≫ next =
      (base).smoothLocus.ι ≫ base :=
  finiteGlobalSmoothAdvanceTo_structure hπ data i (j - i) j (Nat.add_sub_of_le hij) hj

end FLT.Mazur.WeierstrassDividedDepth
