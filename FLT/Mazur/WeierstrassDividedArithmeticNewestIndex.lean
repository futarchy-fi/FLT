/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasIndex

/-!
# Zero retention is the original newest arithmetic chart

The comparison preserves the full tensor morphism, not just its image.
It identifies the last retained depth in the fixed-stage arithmetic atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

omit [IsBezout R] in
/-- With no later modification the retained integral chart is exactly the newest atlas map. -/
theorem olderSuccessiveChart_zero_eq_newest :
    olderSuccessiveChart hπ data j hj 0 hj = finiteAtlasMap hπ data E₀ (j + 1) hj 1 := by
  have h := olderSuccessiveChart_eq_index hπ data j hj 0 hj
  simp only [eqToHom_refl, Category.id_comp] at h
  apply eq_of_heq ((heq_of_eq h.symm).trans ?_)
  congr 1

omit [IsBezout R] in
/-- Zero retention preserves the original newest tensor morphism over any coefficient algebra. -/
theorem olderSuccessiveTensorChart_zero_eq_newest (S : Type) [CommRing S] [Algebra R S] :
    olderSuccessiveTensorChart hπ data j hj 0 hj S =
      finiteSuccessiveTensorChart hπ data S j hj := by
  apply pullback.hom_ext
  · simp only [olderSuccessiveTensorChart, finiteSuccessiveTensorChart, TensorOpenChart.chart_fst]
  · simp only [olderSuccessiveTensorChart, finiteSuccessiveTensorChart, TensorOpenChart.chart_snd,
      olderSuccessiveChart_zero_eq_newest]

/-- The full original arithmetic tensor maps agree when the retention parameter is zero. -/
theorem finiteArithmeticOlderTensorChart_zero (m : ℕ) :
    finiteArithmeticOlderTensorChart hπ data m j hj 0 hj =
      finiteArithmeticNewestTensorChart hπ data m j hj := by
  unfold finiteArithmeticOlderTensorChart finiteArithmeticNewestTensorChart
    olderGlobalTensorChart globalSuccessiveTensorChart
  rw [olderSuccessiveTensorChart_zero_eq_newest]

/-- The last fixed-stage retained index is the actual newest arithmetic tensor chart. -/
theorem arithmeticRetainedTensorChart_newest (m : ℕ) :
    arithmeticRetainedTensorChart hπ data m (j + 1) hj j (by omega) =
      finiteArithmeticNewestTensorChart hπ data m j hj := by
  rw [arithmeticRetainedTensorChart_eq hπ data m (j + 1) hj j (by omega) 0 hj,
    finiteArithmeticOlderTensorChart_zero]

end FLT.Mazur.WeierstrassDividedDepth
