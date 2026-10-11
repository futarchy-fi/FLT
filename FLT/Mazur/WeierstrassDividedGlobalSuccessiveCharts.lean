/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalFiniteStep
public import FLT.Mazur.WeierstrassDividedDepthLocalAction

/-!
# Actual normalized charts in the whole finite successor

Every fraction chart of the successive center embeds in the whole next
finite model. Its step contraction is the normalized preceding divided
chart, with the original affine coordinate map retained exactly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "E" => finiteExterior hπ data
  (initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))) j (Nat.le_of_succ_le hj)
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)

/-- The normalized preceding divided chart in the whole finite model. -/
def finiteNormalizedChart : Spec (.of B) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj) :=
  (previousChartIso hπ d e).hom ≫ (E).dividedChart ≫
    finiteLocalChart hπ data j (Nat.le_of_succ_le hj)

instance finiteNormalizedChart_isOpenImmersion :
    IsOpenImmersion (finiteNormalizedChart hπ data j hj) := by
  unfold finiteNormalizedChart
  infer_instance

/-- Normalizing a divided chart preserves all its original affine coordinates. -/
@[reassoc] theorem finiteNormalizedChart_contraction :
    finiteNormalizedChart hπ data j hj ≫
        finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
      Spec.map (CommRingCat.ofHom (previousOriginalMap hπ d e).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [finiteNormalizedChart, Category.assoc, Category.assoc,
    finiteGlobal_divided_contraction, previousChartIso_toCurve]
  rfl

variable
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + j))
    (π * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
    (π * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
    (π ^ 2 * (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)

/-- An actual fraction input in the normalized local replacement. -/
def finiteSuccessiveFractionChart : Spec (.of (BlowupFractionChart.chart I f)) ⟶
    finiteGlobalModel hπ data (j + 1) hj :=
  BlowupRees.fractionChartInclusion I f hf ≫
    (WeierstrassSuccessiveRees.modificationProjIso W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) hπ).inv ≫
    pushout.inr (E).attach (localBoundary hπ d e) ≫ ((E).advanceIso hπ e).inv ≫
    finiteLocalChart hπ data (j + 1) hj

instance finiteSuccessiveFractionChart_isOpenImmersion :
    IsOpenImmersion (finiteSuccessiveFractionChart hπ data j hj f hf) := by
  unfold finiteSuccessiveFractionChart
  infer_instance

/-- The fraction input contracts through the exact existing global step. -/
@[reassoc] theorem finiteSuccessiveFractionChart_step :
    finiteSuccessiveFractionChart hπ data j hj f hf ≫ finiteGlobalStep hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap B (BlowupFractionChart.chart I f))) ≫
        finiteNormalizedChart hπ data j hj := by
  rw [finiteSuccessiveFractionChart, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, finiteGlobalStep_local]
  change _ ≫ _ ≫ _ ≫ ((E).advanceIso hπ e).inv ≫
    (E).stepContraction hπ e ≫ _ = _
  rw [← Exterior.advanceIso_contraction, Category.assoc, Iso.inv_hom_id_assoc,
    Exterior.localReplacement_inr_contraction_assoc]
  change _ ≫ _ ≫ (WeierstrassSuccessiveX.contraction _ _ _ _ _ _ ≫ _) ≫ _ ≫ _ = _
  rw [← WeierstrassSuccessiveRees.modificationProjIso_contraction W
    (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) hπ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    BlowupRees.fractionChartInclusion_contraction_assoc, finiteNormalizedChart]
  rfl

/-- The successor fraction chart retains the actual original cubic input. -/
@[reassoc] theorem finiteSuccessiveFractionChart_contraction :
    finiteSuccessiveFractionChart hπ data j hj f hf ≫
        finiteGlobalContraction hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom (algebraMap B (BlowupFractionChart.chart I f))) ≫
        Spec.map (CommRingCat.ofHom (previousOriginalMap hπ d e).toRingHom) ≫
          integralCurveChart W 2 := by
  rw [← finiteGlobalStep_contraction hπ data j hj,
    finiteSuccessiveFractionChart_step_assoc, finiteNormalizedChart_contraction]

end FLT.Mazur.WeierstrassDividedDepth
