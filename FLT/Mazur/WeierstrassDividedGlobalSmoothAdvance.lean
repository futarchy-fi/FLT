/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalStepSmoothEmbedding

/-!
# Advance a full smooth locus through any finite number of actual steps

Successive unchanged-open embeddings promote every smooth point to a later
stage of the supplied finite family. Their original cubic contraction and
coefficient structure are preserved throughout.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

/-- A single smooth-stage embedding preserves the entire original cubic map. -/
@[reassoc] theorem finiteGlobalStepSmoothEmbedding_contraction (j : ℕ) (hj : j + 1 ≤ n) :
    finiteGlobalStepSmoothEmbedding hπ data j hj ≫
        (finiteGlobalStructure hπ data (j + 1) hj).smoothLocus.ι ≫
          finiteGlobalContraction hπ data (j + 1) hj =
      (finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj)).smoothLocus.ι ≫
        finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) := by
  rw [← finiteGlobalStep_contraction hπ data j hj,
    finiteGlobalStepSmoothEmbedding_step_assoc]

/-- Embed the entire stage-i smooth locus after l further actual finite steps. -/
def finiteGlobalSmoothAdvance (i : ℕ) : (l : ℕ) → (h : i + l ≤ n) →
    (finiteGlobalStructure hπ data i (by omega)).smoothLocus.toScheme ⟶
      (finiteGlobalStructure hπ data (i + l) h).smoothLocus.toScheme
  | 0, _ => 𝟙 _
  | l + 1, h => finiteGlobalSmoothAdvance i l (Nat.le_of_succ_le h) ≫
      finiteGlobalStepSmoothEmbedding hπ data (i + l) h

/-- Advancing zero steps is the identity on the actual smooth scheme. -/
@[simp] theorem finiteGlobalSmoothAdvance_zero (i : ℕ) (hi : i ≤ n) :
    finiteGlobalSmoothAdvance hπ data i 0 hi = 𝟙 _ := rfl

/-- Advancing one further step uses the constructed unchanged-open embedding. -/
theorem finiteGlobalSmoothAdvance_succ (i l : ℕ) (h : i + (l + 1) ≤ n) :
    finiteGlobalSmoothAdvance hπ data i (l + 1) h =
      finiteGlobalSmoothAdvance hπ data i l (Nat.le_of_succ_le h) ≫
        finiteGlobalStepSmoothEmbedding hπ data (i + l) h := rfl

instance finiteGlobalSmoothAdvance_open (i l : ℕ) (h : i + l ≤ n) :
    IsOpenImmersion (finiteGlobalSmoothAdvance hπ data i l h) := by
  induction l with
  | zero => rw [finiteGlobalSmoothAdvance_zero]; infer_instance
  | succ l ih =>
    rw [finiteGlobalSmoothAdvance_succ]
    let _ := ih (Nat.le_of_succ_le h)
    infer_instance

/-- Advancing smooth points preserves the entire original cubic contraction. -/
@[reassoc] theorem finiteGlobalSmoothAdvance_contraction (i l : ℕ) (h : i + l ≤ n) :
    finiteGlobalSmoothAdvance hπ data i l h ≫
        (finiteGlobalStructure hπ data (i + l) h).smoothLocus.ι ≫
          finiteGlobalContraction hπ data (i + l) h =
      (finiteGlobalStructure hπ data i (by omega)).smoothLocus.ι ≫
        finiteGlobalContraction hπ data i (by omega) := by
  induction l with
  | zero => simp only [Nat.add_zero, finiteGlobalSmoothAdvance_zero, Category.id_comp]
  | succ l ih =>
    simp only [Nat.add_succ, finiteGlobalSmoothAdvance_succ, Category.assoc,
      finiteGlobalStepSmoothEmbedding_contraction]
    exact ih (Nat.le_of_succ_le h)

/-- Advancing smooth points preserves the coefficient point at every finite stage. -/
@[reassoc] theorem finiteGlobalSmoothAdvance_structure (i l : ℕ) (h : i + l ≤ n) :
    finiteGlobalSmoothAdvance hπ data i l h ≫
        (finiteGlobalStructure hπ data (i + l) h).smoothLocus.ι ≫
          finiteGlobalStructure hπ data (i + l) h =
      (finiteGlobalStructure hπ data i (by omega)).smoothLocus.ι ≫
        finiteGlobalStructure hπ data i (by omega) := by
  exact finiteGlobalSmoothAdvance_contraction_assoc hπ data i l h
    (WeierstrassIntegralChart.integralCurveStructure W)

end FLT.Mazur.WeierstrassDividedDepth
