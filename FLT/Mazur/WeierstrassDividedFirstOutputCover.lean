/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstActionInput
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior

/-!
# A complete output atlas for the first whole successor action

Infinity, retained initial exterior, and normalized divided outputs cover
the actual preceding global model. Pulling back along the existing initial
action covers the entire first-successor action source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "E" => initialExterior d

/-- The three original output chart schemes needed by the first successor action. -/
def firstOutputAtlasObject : Option Bool → Scheme.{u}
  | none => chartScheme W 1
  | some false => (E).carrier
  | some true => Spec (.of B)

/-- Their actual embeddings in the complete preceding global model. -/
def firstOutputAtlasMap (j : Option Bool) : firstOutputAtlasObject data hn j ⟶
    finiteGlobalModel hπ data 0 (Nat.zero_le n) :=
  match j with
  | none => finiteInfinityChart hπ data 0 (Nat.zero_le n)
  | some false => finitePrecedingExteriorChart hπ data 0 hn
  | some true => finiteNormalizedChart hπ data 0 hn

instance firstOutputAtlasMap_isOpenImmersion (j : Option Bool) :
    IsOpenImmersion (firstOutputAtlasMap hπ data hn j) := by
  rcases j with _ | (_ | _) <;> dsimp only [firstOutputAtlasMap] <;> infer_instance

/-- Every point of the preceding whole model belongs to one of these actual output charts. -/
theorem firstOutputAtlas_covers (z : finiteGlobalModel hπ data 0 (Nat.zero_le n)) :
    ∃ j x, firstOutputAtlasMap hπ data hn j x = z := by
  rcases finiteGlobal_charts_cover hπ data 0 (Nat.zero_le n) z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨none, x, rfl⟩
  · rcases SchemeOpenPushout.charts_cover (E).attach (boundaryInclusion d) x with
      ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨some false, y, rfl⟩
    · refine ⟨some true, (previousChartIso hπ d e).inv y, ?_⟩
      have he : (previousChartIso hπ d e).hom ((previousChartIso hπ d e).inv y) = y := by
        change ((previousChartIso hπ d e).inv ≫ (previousChartIso hπ d e).hom) y = y
        rw [Iso.inv_hom_id]
        rfl
      change finiteLocalChart hπ data 0 (Nat.zero_le n)
        ((E).dividedChart ((previousChartIso hπ d e).hom ((previousChartIso hπ d e).inv y))) = _
      rw [he]
      rfl

/-- The complete three-chart preceding-output cover. -/
def firstOutputOpenCover : (finiteGlobalModel hπ data 0 (Nat.zero_le n)).OpenCover where
  I₀ := Option Bool
  X := firstOutputAtlasObject data hn
  f := firstOutputAtlasMap hπ data hn
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨firstOutputAtlas_covers hπ data hn, fun _ => inferInstance⟩

/-- The three actual output domains cover the entire first-successor action source. -/
def firstActionOutputCover : (finiteGlobalActionProduct hπ data 1 hn).OpenCover :=
  (firstOutputOpenCover hπ data hn).pullback₁ (firstActionOutput hπ data hn)

end FLT.Mazur.WeierstrassDividedDepth
