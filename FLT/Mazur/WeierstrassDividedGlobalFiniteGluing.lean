/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteYBoundary

/-!
# The whole projective cubic modification at every finite divided depth

Glue the original chart at infinity to the actual finite local model along
its full unchanged original Y-boundary. The resulting contraction retains
both the original infinity map and the existing finite local contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart

/-- The entire projective model at a finite actual divided depth. -/
def finiteGlobalModel : Scheme :=
  pushout (affineBoundaryToY W) (finiteYBoundary hπ data j hj)

/-- The original Y-chart retained at infinity in every finite global model. -/
def finiteInfinityChart : chartScheme W 1 ⟶ finiteGlobalModel hπ data j hj := pushout.inl _ _

/-- The existing actual finite local model as an open of the entire projective model. -/
def finiteLocalChart : finiteModification hπ data j hj ⟶ finiteGlobalModel hπ data j hj :=
  pushout.inr _ _

instance finiteInfinityChart_isOpenImmersion :
    IsOpenImmersion (finiteInfinityChart hπ data j hj) := by
  unfold finiteInfinityChart
  infer_instance

instance finiteLocalChart_isOpenImmersion : IsOpenImmersion (finiteLocalChart hπ data j hj) := by
  unfold finiteLocalChart
  infer_instance

/-- The actual contraction from the whole finite model to the same original projective cubic. -/
def finiteGlobalContraction : finiteGlobalModel hπ data j hj ⟶ integralCurve W :=
  SchemeOpenReplacement.contraction (affineBoundaryToY W) (overlapInclusion W 2 1)
    (finiteYBoundary hπ data j hj) (finiteToAffine hπ data j hj)
    (finiteYBoundary_contraction hπ data j hj) ≫ (yzPushoutIso W).hom

/-- The global finite contraction is unchanged on the entire original chart at infinity. -/
@[reassoc] theorem finiteInfinityChart_contraction :
    finiteInfinityChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      integralCurveChart W 1 := by
  rw [finiteInfinityChart, finiteGlobalContraction,
    SchemeOpenReplacement.inl_contraction_assoc, inl_yzPushoutIso]

/-- The global model retains precisely the already constructed finite local map. -/
@[reassoc] theorem finiteLocalChart_contraction :
    finiteLocalChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      finiteToCurve hπ data j hj := by
  rw [finiteLocalChart, finiteGlobalContraction,
    SchemeOpenReplacement.inr_contraction_assoc, inr_yzPushoutIso, finiteToAffine_toCurve]

/-- These two actual charts cover the whole finite projective model. -/
theorem finiteGlobal_charts_cover (z : finiteGlobalModel hπ data j hj) :
    (∃ a, finiteInfinityChart hπ data j hj a = z) ∨
      ∃ a, finiteLocalChart hπ data j hj a = z :=
  SchemeOpenPushout.charts_cover _ _ z

/-- The final divided chart retains its actual original-cubic contraction globally. -/
@[reassoc] theorem finiteGlobal_divided_contraction :
    (finiteExterior hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj).dividedChart ≫
        finiteLocalChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      toCurve (data ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rw [finiteLocalChart_contraction, finiteDivided_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
