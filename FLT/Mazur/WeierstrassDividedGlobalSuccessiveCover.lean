/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalSuccessiveCharts
public import FLT.Mazur.BlowupReesGeneratorCover

/-!
# A complete successor atlas with fraction inputs and retained charts

The original infinity chart, the retained preceding exterior and the
three fraction charts of the successive center cover the whole successor.
This atlas retains the exceptional fiber and every crossed-input case.
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

local notation "g" => WeierstrassSuccessiveRees.centerGenerators W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "hg" => WeierstrassSuccessiveRees.centerGenerators_mem W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "v" => WeierstrassSuccessiveRees.modificationProjIso W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) hπ

/-- The retained preceding exterior inside the actual whole successor. -/
def finiteSuccessiveRetainedChart : (E).carrier ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  pushout.inl (E).attach (localBoundary hπ d e) ≫ ((E).advanceIso hπ e).inv ≫
    finiteLocalChart hπ data (j + 1) hj

instance finiteSuccessiveRetainedChart_isOpenImmersion :
    IsOpenImmersion (finiteSuccessiveRetainedChart hπ data j hj) := by
  unfold finiteSuccessiveRetainedChart
  infer_instance

/-- The complete successor atlas: infinity, retained exterior, and center fraction charts. -/
def finiteSuccessiveAtlasObject : Option (Option (Fin 3)) → Scheme
  | none => chartScheme W 1
  | some none => (E).carrier
  | some (some i) => Spec (.of (BlowupFractionChart.chart I (g i)))

/-- Actual chart embeddings into the whole successor. -/
def finiteSuccessiveAtlasMap (i : Option (Option (Fin 3))) :
    finiteSuccessiveAtlasObject hπ data j hj i ⟶ finiteGlobalModel hπ data (j + 1) hj :=
  match i with
  | none => finiteInfinityChart hπ data (j + 1) hj
  | some none => finiteSuccessiveRetainedChart hπ data j hj
  | some (some i) => finiteSuccessiveFractionChart hπ data j hj (g i) (hg i)

instance finiteSuccessiveAtlasMap_isOpenImmersion (i : Option (Option (Fin 3))) :
    IsOpenImmersion (finiteSuccessiveAtlasMap hπ data j hj i) := by
  rcases i with _ | (_ | i) <;> dsimp only [finiteSuccessiveAtlasMap] <;> infer_instance

/-- Every point of the whole successor is in one of the actual retained or fraction charts. -/
theorem finiteSuccessiveAtlas_covers (z : finiteGlobalModel hπ data (j + 1) hj) :
    ∃ i x, finiteSuccessiveAtlasMap hπ data j hj i x = z := by
  rcases finiteGlobal_charts_cover hπ data (j + 1) hj z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨none, x, rfl⟩
  · let a := ((E).advanceIso hπ e).hom x
    have hx : ((E).advanceIso hπ e).inv a = x := by
      change (((E).advanceIso hπ e).hom ≫ ((E).advanceIso hπ e).inv) x = x
      rw [Iso.hom_inv_id]
      rfl
    rcases SchemeOpenPushout.charts_cover (E).attach (localBoundary hπ d e) a with
      ⟨y, hy⟩ | ⟨y, hy⟩
    · refine ⟨some none, y, ?_⟩
      change finiteLocalChart hπ data (j + 1) hj
        (((E).advanceIso hπ e).inv (pushout.inl (E).attach (localBoundary hπ d e) y)) = _
      rw [hy, hx]
    · obtain ⟨i, t, ht⟩ := BlowupRees.exists_fractionChart I g hg
        (WeierstrassSuccessiveRees.centerGenerators_span W (π ^ (start + j)) π
          (e).b3 (e).b4 (e).b6) ((v).hom y)
      have ht' : (v).inv (BlowupRees.fractionChartInclusion I (g i) (hg i) t) = y := by
        rw [ht]
        change ((v).hom ≫ (v).inv) y = y
        rw [Iso.hom_inv_id]
        rfl
      refine ⟨some (some i), t, ?_⟩
      change finiteLocalChart hπ data (j + 1) hj
        (((E).advanceIso hπ e).inv (pushout.inr (E).attach (localBoundary hπ d e)
          ((v).inv (BlowupRees.fractionChartInclusion I (g i) (hg i) t)))) = _
      rw [ht', hy, hx]

/-- Package the complete actual successor charts as a finite open cover. -/
def finiteSuccessiveOpenCover : (finiteGlobalModel hπ data (j + 1) hj).OpenCover where
  I₀ := Option (Option (Fin 3))
  X := finiteSuccessiveAtlasObject hπ data j hj
  f := finiteSuccessiveAtlasMap hπ data j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨finiteSuccessiveAtlas_covers hπ data j hj, fun _ => inferInstance⟩

end FLT.Mazur.WeierstrassDividedDepth
