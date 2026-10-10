/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderSuccessiveCharts

/-!
# The exact index of each retained successive chart

A chart created at stage j+1 is exterior index r after r further steps.
The agreement is of the actual morphisms, including the canonical transport
of their dependent source schemes, and not only of their image sets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

omit [IsDomain R] in
/-- Exterior index r is exactly the original successive equation scheme after r further steps. -/
theorem finiteOlderExteriorObject_eq (r : ℕ) (hr : j + 1 + r ≤ n) :
    finiteExteriorAtlasObject data E₀ (j + 1 + r) hr ⟨r, by omega⟩ = stepX e := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (Nat.le_of_succ_le hr)

/-- The indexed exterior atlas map is the constructed retained successive chart. -/
@[reassoc] theorem finiteOlderExteriorMap_eq (r : ℕ) (hr : j + 1 + r ≤ n) :
    eqToHom (finiteOlderExteriorObject_eq data j hj r hr).symm ≫
      finiteExteriorAtlasMap hπ data E₀ (j + 1 + r) hr ⟨r, by omega⟩ =
        (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX hπ e ≫
          finiteStageRetained hπ data (j + 1) hj r hr := by
  induction r with
  | zero =>
    change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]
    rfl
  | succ r ih =>
    change eqToHom (finiteOlderExteriorObject_eq data j hj r (Nat.le_of_succ_le hr)).symm ≫
      (finiteExteriorAtlasMap hπ data E₀ (j + 1 + r) (Nat.le_of_succ_le hr) ⟨r, by omega⟩ ≫
        (finiteExterior hπ data E₀ (j + 1 + r) (Nat.le_of_succ_le hr)).retained hπ _) =
      (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX hπ e ≫
        (finiteStageRetained hπ data (j + 1) hj r (Nat.le_of_succ_le hr) ≫ _)
    rw [← Category.assoc, ih, Category.assoc]
    rfl

/-- The older successive embedding is precisely full-atlas index r+1. -/
@[reassoc] theorem olderSuccessiveChart_eq_index (r : ℕ) (hr : j + 1 + r ≤ n) :
    eqToHom (finiteOlderExteriorObject_eq data j hj r hr).symm ≫
      finiteAtlasMap hπ data E₀ (j + 1 + r) hr ⟨r + 1, by omega⟩ =
        olderSuccessiveChart hπ data j hj r hr := by
  change eqToHom _ ≫ (finiteExteriorAtlasMap hπ data E₀ _ _ _ ≫ _) = _
  rw [← Category.assoc, finiteOlderExteriorMap_eq]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
