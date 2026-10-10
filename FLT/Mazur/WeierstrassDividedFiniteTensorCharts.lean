/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartRange
public import FLT.Mazur.WeierstrassDividedFiniteFlat
public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.WeierstrassDilatationBaseChange

/-!
# Actual tensor charts in the finite integral atlas

The final divided chart and newest successive chart are identified with the
pullbacks of their original integral atlas maps. This retains the whole
charts, their coefficient structures, and their original-cubic contractions.
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
  (S : Type u) [CommRing S] [Algebra R S]
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The actual coefficient extension of the finite integral model. -/
def finiteTensorModel (j : ℕ) (hj : j ≤ n) : Scheme :=
  pullback q (finiteStructure hπ data j hj)

/-- The terminal divided atlas chart has its original algebra structure. -/
@[reassoc] theorem finiteDivided_structure (j : ℕ) (hj : j ≤ n) :
    (finiteExterior hπ data E₀ j hj).dividedChart ≫ finiteStructure hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassDilatation.Coordinate W (π ^ (start + j))
          (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
          (data ⟨j, Nat.lt_succ_of_le hj⟩).b6))) := by
  rw [finiteStructure, finiteDivided_toCurve_assoc, toCurve_structure]

/-- The final divided tensor algebra is an actual open of the finite base change. -/
def finiteDividedTensorChart (j : ℕ) (hj : j ≤ n) :
    Spec (.of (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 S)) ⟶ finiteTensorModel hπ data S j hj :=
  TensorOpenChart.chart _ _ (finiteDivided_structure hπ data j hj)

instance finiteDividedTensorChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteDividedTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- The newest successive atlas chart has its original three-coordinate algebra structure. -/
@[reassoc] theorem finiteSuccessive_structure (j : ℕ) (hj : j + 1 ≤ n) :
    (finiteAtlasMap hπ data E₀ (j + 1) hj 1) ≫ finiteStructure hπ data (j + 1) hj =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))) := by
  change (finiteExteriorAtlasMap hπ data E₀ (j + 1) hj 0 ≫
    (finiteExterior hπ data E₀ (j + 1) hj).exteriorChart) ≫ _ = _
  rw [finiteStructure, Category.assoc, finiteExteriorAtlas_new_toCurve_assoc,
    xContraction_structure]

/-- The actual successive tensor algebra embeds into the finite coefficient extension. -/
def finiteSuccessiveTensorChart (j : ℕ) (hj : j + 1 ≤ n) :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 S)) ⟶
        finiteTensorModel hπ data S (j + 1) hj :=
  TensorOpenChart.chart _ _ (finiteSuccessive_structure hπ data j hj)

instance finiteSuccessiveTensorChart_isOpenImmersion (j : ℕ) (hj : j + 1 ≤ n) :
    IsOpenImmersion (finiteSuccessiveTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- The newest tensor chart is precisely the pullback of its original integral atlas chart. -/
theorem finiteSuccessiveTensorChart_isPullback (j : ℕ) (hj : j + 1 ≤ n) :
    IsPullback (finiteSuccessiveTensorChart hπ data S j hj) (TensorOpenChart.projection)
      (pullback.snd q (finiteStructure hπ data (j + 1) hj))
      (finiteAtlasMap hπ data E₀ (j + 1) hj 1) :=
  TensorOpenChart.chart_isPullback _ _ _

/-- The same cartesian comparison holds for the actual terminal divided chart. -/
theorem finiteDividedTensorChart_isPullback (j : ℕ) (hj : j ≤ n) :
    IsPullback (finiteDividedTensorChart hπ data S j hj) (TensorOpenChart.projection)
      (pullback.snd q (finiteStructure hπ data j hj))
      (finiteExterior hπ data E₀ j hj).dividedChart :=
  TensorOpenChart.chart_isPullback _ _ _

end FLT.Mazur.WeierstrassDividedDepth
