/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthMaps
public import FLT.Mazur.WeierstrassDividedFiniteIteration
public import FLT.Mazur.WeierstrassDividedInitialExterior

/-!
# Finite whole contraction retains the actual divided coordinates

The restriction of the composite whole contraction is the direct actual
depth transition. Starting from the original two-chart modification gives
an arbitrary finite construction over the same original projective cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (E : Exterior (data ⟨0, Nat.zero_lt_succ n⟩))

/-- On every final divided chart the composite whole map is the direct depth transition. -/
@[reassoc] theorem finiteDivided_contraction (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ data E j hj).dividedChart ≫ finiteContraction hπ data E j hj =
      depthMap hπ (data ⟨0, Nat.zero_lt_succ n⟩) (data ⟨j, Nat.lt_succ_of_le hj⟩)
        (Nat.le_add_right start j) ≫ E.dividedChart := by
  induction j with
  | zero => simp [finiteContraction, finiteWhole, finiteExterior]
  | succ j ih =>
    simp only [finiteContraction, finiteStep, finiteExterior,
      Exterior.dividedChart_stepContraction_assoc]
    rw [ih (Nat.le_of_succ_le hj), transition_eq_depthMap, depthMap_comp_assoc]

/-- The actual finite whole construction beginning with the original modification. -/
def finiteModification (j : ℕ) (hj : j ≤ n) : Scheme :=
  finiteWhole hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj

/-- The finite construction retains a morphism to the original projective cubic. -/
def finiteToCurve (j : ℕ) (hj : j ≤ n) :
    finiteModification hπ data j hj ⟶ WeierstrassIntegralChart.integralCurve W :=
  finiteContraction hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
    initialToCurve (data ⟨0, Nat.zero_lt_succ n⟩)

/-- The final actual divided chart retains precisely the original cubic contraction. -/
@[reassoc] theorem finiteDivided_toCurve (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj).dividedChart ≫
        finiteToCurve hπ data j hj = toCurve (data ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rw [finiteToCurve, finiteDivided_contraction_assoc, initialToCurve_divided, depthMap_toCurve]

/-- The original exterior remains unchanged over the same projective cubic. -/
@[reassoc] theorem finiteExterior_toCurve (j : ℕ) (hj : j ≤ n) :
    finiteRetained hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
      (finiteExterior hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj).exteriorChart ≫
        finiteToCurve hπ data j hj =
      (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)).exteriorChart ≫
        initialToCurve (data ⟨0, Nat.zero_lt_succ n⟩) := by
  rw [finiteToCurve, finiteRetained_contraction_assoc]

end FLT.Mazur.WeierstrassDividedDepth
