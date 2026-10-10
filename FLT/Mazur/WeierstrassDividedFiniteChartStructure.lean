/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteAtlas
public import FLT.Mazur.WeierstrassDividedFiniteContraction

/-!
# Contractions on the finite exterior atlas

Seal the successor restriction formulas without expanding the recursively
glued schemes. These formulas retain the actual map of each original chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- A finite contraction to the original cubic factors through its preceding whole step. -/
@[reassoc] theorem finiteToCurve_succ (j : ℕ) (hj : j + 1 ≤ n) :
    finiteToCurve hπ data (j + 1) hj =
      finiteStep hπ data E₀ j hj ≫ finiteToCurve hπ data j (Nat.le_of_succ_le hj) := by
  simp only [finiteToCurve, finiteContraction, Category.assoc]

/-- The newest exterior atlas chart retains its actual successive coordinate contraction. -/
@[reassoc] theorem finiteExteriorAtlas_new_toCurve (j : ℕ) (hj : j + 1 ≤ n) :
    finiteExteriorAtlasMap hπ data E₀ (j + 1) hj 0 ≫
      (finiteExterior hπ data E₀ (j + 1) hj).exteriorChart ≫
        finiteToCurve hπ data (j + 1) hj =
      xContraction hπ (data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩)
        (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) ≫
          toCurve (data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩) := by
  rw [finiteToCurve_succ]
  change (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX hπ _ ≫
    ((finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).advance hπ _).exteriorChart ≫
      (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).stepContraction hπ _ ≫ _ = _
  rw [Exterior.exteriorChart_stepContraction_assoc, Exterior.newX_contraction_assoc,
    finiteDivided_toCurve]

/-- Every older exterior atlas chart retains its original-cubic map after one more step. -/
@[reassoc] theorem finiteExteriorAtlas_old_toCurve (j : ℕ) (hj : j + 1 ≤ n)
    (i : Fin (j + 1)) :
    finiteExteriorAtlasMap hπ data E₀ (j + 1) hj i.succ ≫
      (finiteExterior hπ data E₀ (j + 1) hj).exteriorChart ≫
        finiteToCurve hπ data (j + 1) hj =
      finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i ≫
        (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).exteriorChart ≫
          finiteToCurve hπ data j (Nat.le_of_succ_le hj) := by
  rw [finiteToCurve_succ]
  change (finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i ≫
    (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).retained hπ _) ≫
      ((finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).advance hπ _).exteriorChart ≫
        (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).stepContraction hπ _ ≫ _ = _
  rw [Category.assoc, Exterior.exteriorChart_stepContraction_assoc,
    Exterior.retained_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
