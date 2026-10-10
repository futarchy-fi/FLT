/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteChartStructure

/-!
# Retaining every finite exterior through later stages

Each intermediate exterior embeds in every later exterior. Its original
cubic contraction is unchanged by the entire subsequent modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- Retain an intermediate exterior through any available number of later stages. -/
def finiteStageRetained : (r : ℕ) → (hr : j + r ≤ n) →
    (finiteExterior hπ data E₀ j hj).carrier ⟶
      (finiteExterior hπ data E₀ (j + r) hr).carrier
  | 0, _ => 𝟙 _
  | r + 1, hr => finiteStageRetained r (Nat.le_of_succ_le hr) ≫
    (finiteExterior hπ data E₀ (j + r) (Nat.le_of_succ_le hr)).retained hπ
      (data ⟨j + r + 1, Nat.lt_succ_of_le hr⟩)

instance finiteStageRetained_isOpenImmersion (r : ℕ) (hr : j + r ≤ n) :
    IsOpenImmersion (finiteStageRetained hπ data j hj r hr) := by
  induction r with
  | zero => change IsOpenImmersion (𝟙 _); infer_instance
  | succ r ih =>
    let _ := ih (Nat.le_of_succ_le hr)
    dsimp only [finiteStageRetained]
    infer_instance

/-- Every retained exterior keeps its original cubic map after all later steps. -/
@[reassoc] theorem finiteStageRetained_toCurve (r : ℕ) (hr : j + r ≤ n) :
    finiteStageRetained hπ data j hj r hr ≫
      (finiteExterior hπ data E₀ (j + r) hr).exteriorChart ≫
        finiteToCurve hπ data (j + r) hr =
      (finiteExterior hπ data E₀ j hj).exteriorChart ≫ finiteToCurve hπ data j hj := by
  induction r with
  | zero => simp only [finiteStageRetained, Category.id_comp, Nat.add_zero]
  | succ r ih =>
    conv_lhs =>
      arg 2
      arg 2
      change finiteToCurve hπ data (j + r + 1) hr
      rw [finiteToCurve_succ]
    change (finiteStageRetained hπ data j hj r (Nat.le_of_succ_le hr) ≫
      (finiteExterior hπ data E₀ (j + r) (Nat.le_of_succ_le hr)).retained hπ _) ≫
        ((finiteExterior hπ data E₀ (j + r) (Nat.le_of_succ_le hr)).advance hπ _).exteriorChart ≫
          (finiteExterior hπ data E₀ (j + r) (Nat.le_of_succ_le hr)).stepContraction hπ _ ≫
            finiteToCurve hπ data (j + r) (Nat.le_of_succ_le hr) = _
    rw [Category.assoc, Exterior.exteriorChart_stepContraction_assoc,
      Exterior.retained_contraction_assoc]
    exact ih (Nat.le_of_succ_le hr)

end FLT.Mazur.WeierstrassDividedDepth
