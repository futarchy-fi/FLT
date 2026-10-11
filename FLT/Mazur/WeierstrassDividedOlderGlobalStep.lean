/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedGlobalStepOriginal
public import FLT.Mazur.WeierstrassDividedFiniteExteriorPullback

/-!
# Full retained successive charts under the actual global steps

The older successive equation chart is unchanged by every later global step.
Its full pullback square gives uniqueness for arbitrary schemes of points,
including residue schemes that are not flat over the original base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

/-- The actual integral older equation chart in each later global model. -/
def olderGlobalChart (r : ℕ) (hr : j + 1 + r ≤ n) :=
  olderSuccessiveChart hπ data j hj r hr ≫ finiteLocalChart hπ data (j + 1 + r) hr

instance olderGlobalChart_isOpenImmersion (r : ℕ) (hr : j + 1 + r ≤ n) :
    IsOpenImmersion (olderGlobalChart hπ data j hj r hr) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The retained integral chart has its original coefficient morphism. -/
@[reassoc] theorem olderGlobalChart_structure (r : ℕ) (hr : j + 1 + r ≤ n) :
    olderGlobalChart hπ data j hj r hr ≫
        finiteGlobalStructure hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
          (Data.b3 e) (Data.b4 e) (Data.b6 e)))) := by
  rw [olderGlobalChart, Category.assoc, finiteLocalChart_structure,
    olderSuccessiveChart_structure]

/-- Every later global step has the identity pullback over the full older chart. -/
theorem olderGlobalChart_step_isPullback (r : ℕ) (hr : j + 1 + (r + 1) ≤ n) :
    IsPullback (𝟙 (stepX e)) (olderGlobalChart hπ data j hj (r + 1) hr)
      (olderGlobalChart hπ data j hj r (by omega))
      (finiteGlobalStep hπ data (j + 1 + r) hr) := by
  have H := (IsPullback.of_id_fst
    (f := (finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)).newX hπ e ≫
      finiteStageRetained hπ data (j + 1) hj r (by omega))).paste_vert
        ((finiteExterior hπ data E₀ (j + 1 + r) (by omega)).step_exterior_isPullback
          hπ (data ⟨j + 1 + r + 1, by omega⟩))
  have H' := H.paste_vert (finiteGlobalStep_local_isPullback hπ data (j + 1 + r) hr)
  convert H' using 1 <;>
    simp only [olderGlobalChart, olderSuccessiveChart, finiteStageRetained,
      finiteExterior, Category.assoc]
  rfl

/-- The original older chart commutes with the actual global contraction. -/
@[reassoc] theorem olderGlobalChart_step (r : ℕ) (hr : j + 1 + (r + 1) ≤ n) :
    olderGlobalChart hπ data j hj (r + 1) hr ≫
        finiteGlobalStep hπ data (j + 1 + r) hr =
      olderGlobalChart hπ data j hj r (by omega) := by
  simpa only [Category.id_comp] using (olderGlobalChart_step_isPullback hπ data j hj r hr).w.symm

/-- Any point lying over the unchanged older chart is its unique displayed lift. -/
theorem olderGlobalChart_step_lift_unique (r : ℕ) (hr : j + 1 + (r + 1) ≤ n)
    {T : Scheme.{u}} (x : T ⟶ stepX e)
    (f : T ⟶ finiteGlobalModel hπ data (j + 1 + (r + 1)) hr)
    (hf : f ≫ finiteGlobalStep hπ data (j + 1 + r) hr =
      x ≫ olderGlobalChart hπ data j hj r (by omega)) :
    f = x ≫ olderGlobalChart hπ data j hj (r + 1) hr := by
  have H := olderGlobalChart_step_isPullback hπ data j hj r hr
  have hx := H.lift_fst x f hf.symm
  simp only [Category.comp_id] at hx
  have hy := H.lift_snd x f hf.symm
  rw [hx] at hy
  exact hy.symm

/-- The older tensor map projects to this same integral chart. -/
@[reassoc] theorem olderGlobalTensorChart_integralProjection
    (S : Type u) [CommRing S] [Algebra R S] (r : ℕ) (hr : j + 1 + r ≤ n) :
    olderGlobalTensorChart hπ data S j hj r hr ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (finiteGlobalStructure hπ data (j + 1 + r) hr) =
      TensorOpenChart.projection ≫ olderGlobalChart hπ data j hj r hr := by
  rw [olderGlobalTensorChart, Category.assoc, finiteLocalTensorEmbedding_square]
  change _ ≫ _ ≫ _ = _
  rw [← Category.assoc]
  change (TensorOpenChart.chart _ _ _ ≫ _) ≫ _ = _
  rw [TensorOpenChart.chart_snd, Category.assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
