/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentIntegralBoundary
public import FLT.Mazur.WeierstrassDividedRetentionSuccessor

/-!
# Adjacent original boundaries after every later retention

The common boundary equality survives every subsequent exterior inclusion.
The old chart is transported only across equality of its natural-number
stage index, so it remains the original retained chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "F" => Exterior.advance hπ (E) e
local notation "tail" => finiteStageRetained hπ data (j + 2) hjNext r hr
local notation "ext" => Exterior.exteriorChart (finiteExterior hπ data E₀ (j + 2 + r) hr)

/-- Reassociating an equal finite stage does not change its actual whole model. -/
theorem finiteModification_index_congr {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    finiteModification hπ data a ha = finiteModification hπ data b hb := by
  subst b
  rfl

/-- The original exterior inclusion is independent of a presentation of its stage index. -/
theorem finiteExterior_chart_heq {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : a = b) :
    HEq ((finiteExterior hπ data E₀ a ha).exteriorChart)
      ((finiteExterior hπ data E₀ b hb).exteriorChart) := by
  subst b
  rfl

/-- The original older chart, with only its target stage index reassociated. -/
def adjacentRetainedOldChart : stepX e ⟶ finiteModification hπ data (j + 2 + r) hr :=
  olderSuccessiveChart hπ data j hj (r + 1) (by omega) ≫
    eqToHom (finiteModification_index_congr hπ data (by omega) (by omega) (by omega))

/-- The old chart is the original new-X inclusion followed by all actual later retentions. -/
@[reassoc] theorem adjacentRetainedOldChart_eq :
    adjacentRetainedOldChart hπ data j hj r hr =
      (E).newX hπ e ≫ (F).retained hπ fData ≫ tail ≫ ext := by
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  change HEq ((E).newX hπ e ≫
    finiteStageRetained hπ data (j + 1) hj (r + 1) (by omega) ≫
      (finiteExterior hπ data E₀ (j + 1 + (r + 1)) (by omega)).exteriorChart) _
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  apply heq_comp rfl
    (finiteExterior_carrier_congr hπ data (by omega) (by omega) (by omega))
    (finiteModification_index_congr hπ data (by omega) (by omega) (by omega))
  · rw [Category.assoc]
    apply heq_comp rfl rfl
      (finiteExterior_carrier_congr hπ data (by omega) (by omega) (by omega)) HEq.rfl
    exact finiteStageRetained_succ_left hπ data (j + 1) hj hjNext r (by omega)
  exact finiteExterior_chart_heq hπ data (by omega) (by omega) (by omega)

/-- Every later pair of adjacent charts keeps its entire original integral boundary. -/
@[reassoc] theorem adjacentRetainedIntegral_boundary :
    nextToX e ≫ adjacentRetainedOldChart hπ data j hj r hr =
      previousToX hπ e fData ≫ olderSuccessiveChart hπ data (j + 1) hjNext r hr := by
  rw [adjacentRetainedOldChart_eq hπ data j hj hjNext r hr]
  change nextToX e ≫ (E).newX hπ e ≫ (F).retained hπ fData ≫ tail ≫ ext =
    previousToX hπ e fData ≫ (F).newX hπ fData ≫ tail ≫ ext
  have H := pushout.condition_assoc (f := (F).attach)
    (g := previousToX hπ e fData) (tail ≫ ext)
  change (nextToX e ≫ (E).newX hπ e) ≫ _ ≫ _ = _ at H
  simpa only [Category.assoc, Exterior.newX, Exterior.retained] using H

open WeierstrassSuccessiveX
local notation "a" => depthOverlapEquiv W π (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "b" => previousBoundaryEquiv hπ e fData
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "i" => adjacentRetainedOldChart hπ data j hj r hr
local notation "l" => olderSuccessiveChart hπ data (j + 1) hjNext r hr

/-- Both original integral localization maps agree at every later common stage. -/
@[reassoc] theorem adjacentRetainedIntegral_localizations :
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm a).toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t))) ≫ i =
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm b).toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away u))) ≫ l := by
  change Spec.map _ ≫ xOpenInclusion _ _ _ _ _ _ ≫ i =
    Spec.map _ ≫ horizontalOpenInclusion _ _ _ _ _ _ ≫ l
  exact (depthOverlap_inverse_inclusion_assoc e i).trans
    ((adjacentRetainedIntegral_boundary hπ data j hj hjNext r hr).trans
      (previousBoundary_inverse_inclusion_assoc hπ e fData l).symm)

end FLT.Mazur.WeierstrassDividedDepth
