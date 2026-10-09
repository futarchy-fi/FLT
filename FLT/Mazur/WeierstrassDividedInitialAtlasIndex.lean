/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorChart

/-!
# The retained initial chart is the last finite atlas chart

The original ModificationX exterior remains exterior index j at stage j.
This identifies its actual retained map, including when the initial depth is zero.
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

omit [IsDomain R] in
/-- The last exterior atlas object is the original ModificationX equation chart. -/
theorem finiteInitialExteriorObject_eq (j : ℕ) (hj : j ≤ n) :
    finiteExteriorAtlasObject data E₀ j hj ⟨j, by omega⟩ = (E₀).carrier := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih (Nat.le_of_succ_le hj)

/-- The last exterior atlas map is the original finite retention map. -/
@[reassoc] theorem finiteInitialExteriorMap_eq (j : ℕ) (hj : j ≤ n) :
    eqToHom (finiteInitialExteriorObject_eq data j hj).symm ≫
      finiteExteriorAtlasMap hπ data E₀ j hj ⟨j, by omega⟩ =
        finiteRetained hπ data E₀ j hj := by
  induction j with
  | zero => change (𝟙 _) ≫ (𝟙 _) = 𝟙 _; exact Category.id_comp _
  | succ j ih =>
    change eqToHom (finiteInitialExteriorObject_eq data j (Nat.le_of_succ_le hj)).symm ≫
      (finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) ⟨j, by omega⟩ ≫ _) =
        finiteRetained hπ data E₀ j (Nat.le_of_succ_le hj) ≫ _
    rw [← Category.assoc, ih]

/-- The whole retained initial chart is precisely full-atlas index j+1. -/
@[reassoc] theorem finiteInitialChart_eq_index (j : ℕ) (hj : j ≤ n) :
    eqToHom (finiteInitialExteriorObject_eq data j hj).symm ≫
      finiteAtlasMap hπ data E₀ j hj ⟨j + 1, by omega⟩ = finiteInitialChart hπ data j hj := by
  change eqToHom _ ≫ (finiteExteriorAtlasMap hπ data E₀ _ _ _ ≫ _) = _
  rw [← Category.assoc, finiteInitialExteriorMap_eq]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
