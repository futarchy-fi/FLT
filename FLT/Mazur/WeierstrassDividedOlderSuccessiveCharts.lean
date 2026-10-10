/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteStageRetention
public import FLT.Mazur.WeierstrassDividedFiniteTensorGeometry

/-!
# Older successive charts retained in later finite models

An actual successive equation chart remains an open chart after any number
of later modifications. Its tensor algebra embeds in the later coefficient
pullback with the same original-cubic contraction and coefficient structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

/-- The original successive chart at stage j+1 embeds into every available later whole. -/
def olderSuccessiveChart : stepX e ⟶ finiteWhole hπ data E₀ (j + 1 + r) hr :=
  (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX hπ e ≫
    finiteStageRetained hπ data (j + 1) hj r hr ≫
      (finiteExterior hπ data E₀ (j + 1 + r) hr).exteriorChart

instance olderSuccessiveChart_isOpenImmersion :
    IsOpenImmersion (olderSuccessiveChart hπ data j hj r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _))

/-- Later modifications retain the full original contraction of every older chart. -/
@[reassoc] theorem olderSuccessiveChart_toCurve :
    olderSuccessiveChart hπ data j hj r hr ≫ finiteToCurve hπ data (j + 1 + r) hr =
      xContraction hπ d e ≫ toCurve d := by
  rw [olderSuccessiveChart, Category.assoc, Category.assoc, finiteStageRetained_toCurve]
  exact finiteExteriorAtlas_new_toCurve hπ data j hj

/-- The older actual chart keeps the original integral coefficient structure. -/
@[reassoc] theorem olderSuccessiveChart_structure :
    olderSuccessiveChart hπ data j hj r hr ≫ finiteStructure hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
          (Data.b3 e) (Data.b4 e) (Data.b6 e)))) := by
  rw [finiteStructure, olderSuccessiveChart_toCurve_assoc, xContraction_structure]

variable (S : Type u) [CommRing S] [Algebra R S]
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The original older tensor algebra embeds in every later finite coefficient extension. -/
def olderSuccessiveTensorChart :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) S)) ⟶
        finiteTensorModel hπ data S (j + 1 + r) hr :=
  TensorOpenChart.chart _ _ (olderSuccessiveChart_structure hπ data j hj r hr)

instance olderSuccessiveTensorChart_isOpenImmersion :
    IsOpenImmersion (olderSuccessiveTensorChart hπ data j hj r hr S) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- The older tensor chart is the actual pullback of its original retained atlas map. -/
theorem olderSuccessiveTensorChart_isPullback :
    IsPullback (olderSuccessiveTensorChart hπ data j hj r hr S) TensorOpenChart.projection
      (pullback.snd q (finiteStructure hπ data (j + 1 + r) hr))
        (olderSuccessiveChart hπ data j hj r hr) :=
  TensorOpenChart.chart_isPullback _ _ _

/-- Its image is exactly the full inverse image of the original older chart. -/
theorem olderSuccessiveTensorChart_range :
    Set.range (olderSuccessiveTensorChart hπ data j hj r hr S) =
      (pullback.snd q (finiteStructure hπ data (j + 1 + r) hr)) ⁻¹'
        Set.range (olderSuccessiveChart hπ data j hj r hr) :=
  TensorOpenChart.chart_range _ _ _

/-- The retained older tensor chart keeps the extended coefficient structure. -/
@[reassoc] theorem olderSuccessiveTensorChart_structure :
    olderSuccessiveTensorChart hπ data j hj r hr S ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
          (Data.b3 e) (Data.b4 e) (Data.b6 e) S))) :=
  TensorOpenChart.chart_fst _ _ _

/-- Every original function of the older chart retains its cubic contraction after base change. -/
@[reassoc] theorem olderSuccessiveTensorChart_toCurve :
    olderSuccessiveTensorChart hπ data j hj r hr S ≫
      pullback.snd q (finiteStructure hπ data (j + 1 + r) hr) ≫
        finiteToCurve hπ data (j + 1 + r) hr =
      TensorOpenChart.projection ≫ xContraction hπ d e ≫ toCurve d := by
  rw [← Category.assoc]
  change (TensorOpenChart.chart _ _ _ ≫ _) ≫ _ = _
  rw [TensorOpenChart.chart_snd, Category.assoc, olderSuccessiveChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
