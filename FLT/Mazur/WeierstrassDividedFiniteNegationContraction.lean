/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNegation
public import FLT.Mazur.WeierstrassDividedFiniteContraction

/-!
# Finite negatives retain the originally chosen projective equation

The initial whole negative contracts to the original Weierstrass inverse.
Every later finite negative retains this same contraction, the original
coefficient morphism, and the initial exterior at every finite depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "d₀" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "E₀" => initialExterior d₀
local notation "E" => finiteExterior hπ data E₀

/-- The constructed stage-zero whole negative retains the actual original cubic inverse. -/
@[reassoc] theorem finiteWholeInitialNegation_toCurve :
    (finiteWholeNegationIso hπ data 0 (Nat.zero_le n)).hom ≫ initialToCurve d₀ =
      initialToCurve d₀ ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  apply (E 0 (Nat.zero_le n)).hom_ext
  · rw [finiteWholeNegationIso_exterior_assoc]
    change (initialExteriorNegationIso d₀).hom ≫ (E₀).exteriorChart ≫ initialToCurve d₀ =
      (E₀).exteriorChart ≫ initialToCurve d₀ ≫ WeierstrassIntegralChart.integralCurveNegation W
    rw [initialToCurve_exterior, initialToCurve_exterior_assoc]
    exact WeierstrassModificationX.initialReflectionIso_toCurve W (π ^ start)
      (d₀).b3 (d₀).b4 (d₀).b6 (d₀).factor3 (d₀).factor4 (d₀).factor6
  · rw [finiteWholeNegationIso_divided_assoc]
    change (chartNegationIso d₀).hom ≫ (E₀).dividedChart ≫ initialToCurve d₀ =
      (E₀).dividedChart ≫ initialToCurve d₀ ≫ WeierstrassIntegralChart.integralCurveNegation W
    rw [initialToCurve_divided, initialToCurve_divided_assoc, chartNegationIso_toCurve]

/-- Every finite local negative retains the chosen original projective cubic morphism. -/
@[reassoc] theorem finiteWholeNegationIso_toCurve (j : ℕ) (hj : j ≤ n) :
    (finiteWholeNegationIso hπ data j hj).hom ≫ finiteToCurve hπ data j hj =
      finiteToCurve hπ data j hj ≫ WeierstrassIntegralChart.integralCurveNegation W := by
  rw [finiteToCurve, finiteWholeNegationIso_contraction_assoc,
    finiteWholeInitialNegation_toCurve, Category.assoc]

/-- The negative fixes the original coefficient morphism at every finite local stage. -/
@[reassoc] theorem finiteWholeNegationIso_structure (j : ℕ) (hj : j ≤ n) :
    (finiteWholeNegationIso hπ data j hj).hom ≫ finiteToCurve hπ data j hj ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      finiteToCurve hπ data j hj ≫ WeierstrassIntegralChart.integralCurveStructure W := by
  rw [finiteWholeNegationIso_toCurve_assoc,
    WeierstrassIntegralChart.integralCurveNegation_structure]

/-- Every finite exterior negative retains the original initial exterior reflection. -/
@[reassoc] theorem finiteRetained_negation (j : ℕ) (hj : j ≤ n) :
    finiteRetained hπ data E₀ j hj ≫ (finiteExteriorNegationIso hπ data j hj).hom =
      (initialExteriorNegationIso d₀).hom ≫ finiteRetained hπ data E₀ j hj := by
  induction j with
  | zero => simp only [finiteRetained, Category.id_comp, Category.comp_id]; rfl
  | succ j ih =>
    change (finiteRetained hπ data E₀ j (Nat.le_of_succ_le hj) ≫
      (E j (Nat.le_of_succ_le hj)).retained hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) ≫
      ((E j (Nat.le_of_succ_le hj)).advanceNegationIso hπ
        (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)
        (finiteExteriorNegationIso hπ data j (Nat.le_of_succ_le hj))
        (finiteExteriorNegationIso_attach hπ data j (Nat.le_of_succ_le hj))).hom = _
    rw [Category.assoc, Exterior.retained_advanceNegationIso, ← Category.assoc, ih]
    exact Category.assoc _ _ _

end FLT.Mazur.WeierstrassDividedDepth
