/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorActionInput
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior

/-!
# A complete output atlas at every finite successor

Infinity, retained preceding exterior, and normalized divided outputs cover
the actual preceding global model. Pulling back along the preceding
action covers the entire successor action source.
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (k : ℕ) (hk : k + 1 ≤ n)
local notation "e" => data (Fin.mk (k + 1) (Nat.lt_succ_of_le hk))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + k))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + k)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "v" => finiteNormalizedChart hπ data k hk

local notation "d" => data (Fin.mk k (Nat.lt_succ_of_le (Nat.le_of_succ_le hk)))
local notation "E" => finiteExterior hπ data
  (initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))) k (Nat.le_of_succ_le hk)

/-- The three original output chart schemes needed by the successor action. -/
def successorOutputAtlasObject : Option Bool → Scheme.{u}
  | none => chartScheme W 1
  | some false => (E).carrier
  | some true => Spec (.of B)

/-- Their actual embeddings in the complete preceding global model. -/
def successorOutputAtlasMap (j : Option Bool) : successorOutputAtlasObject hπ data k hk j ⟶
    finiteGlobalModel hπ data k (Nat.le_of_succ_le hk) :=
  match j with
  | none => finiteInfinityChart hπ data k (Nat.le_of_succ_le hk)
  | some false => finitePrecedingExteriorChart hπ data k hk
  | some true => finiteNormalizedChart hπ data k hk

instance successorOutputAtlasMap_isOpenImmersion (j : Option Bool) :
    IsOpenImmersion (successorOutputAtlasMap hπ data k hk j) := by
  rcases j with _ | (_ | _) <;> dsimp only [successorOutputAtlasMap] <;> infer_instance

/-- Every point of the preceding whole model belongs to one of these actual output charts. -/
theorem successorOutputAtlas_covers (z : finiteGlobalModel hπ data k (Nat.le_of_succ_le hk)) :
    ∃ j x, successorOutputAtlasMap hπ data k hk j x = z := by
  rcases finiteGlobal_charts_cover hπ data k (Nat.le_of_succ_le hk) z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact ⟨none, x, rfl⟩
  · rcases SchemeOpenPushout.charts_cover (E).attach (boundaryInclusion d) x with
      ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨some false, y, rfl⟩
    · refine ⟨some true, (previousChartIso hπ d e).inv y, ?_⟩
      have he : (previousChartIso hπ d e).hom ((previousChartIso hπ d e).inv y) = y := by
        change ((previousChartIso hπ d e).inv ≫ (previousChartIso hπ d e).hom) y = y
        rw [Iso.inv_hom_id]
        rfl
      change finiteLocalChart hπ data k (Nat.le_of_succ_le hk)
        ((E).dividedChart ((previousChartIso hπ d e).hom ((previousChartIso hπ d e).inv y))) = _
      rw [he]
      rfl

/-- The complete three-chart preceding-output cover. -/
def successorOutputOpenCover : (finiteGlobalModel hπ data k (Nat.le_of_succ_le hk)).OpenCover where
  I₀ := Option Bool
  X := successorOutputAtlasObject hπ data k hk
  f := successorOutputAtlasMap hπ data k hk
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨successorOutputAtlas_covers hπ data k hk, fun _ => inferInstance⟩

variable (a : finiteGlobalActionProduct hπ data k (Nat.le_of_succ_le hk) ⟶
  finiteGlobalModel hπ data k (Nat.le_of_succ_le hk))

/-- The three actual output domains cover the entire successor action source. -/
def successorActionOutputCover : (finiteGlobalActionProduct hπ data (k + 1) hk).OpenCover :=
  (successorOutputOpenCover hπ data k hk).pullback₁ (successorActionOutput hπ data k hk a)

end FLT.Mazur.WeierstrassDividedDepth
