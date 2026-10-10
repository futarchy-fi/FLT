/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteTensorCharts

/-!
# The retained initial ModificationX tensor chart

This is the original initial exterior, including the k=0 case. It is kept
separate from the positive-depth successive charts and retains its original
cubic contraction at every finite stage.
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
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "E₀" => initialExterior d₀
local notation "A₀" => WeierstrassModificationX.Coordinate W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)

/-- The original ModificationX chart retained in the whole finite model. -/
def finiteInitialChart (j : ℕ) (hj : j ≤ n) : Spec (.of A₀) ⟶ finiteModification hπ data j hj :=
  finiteRetained hπ data E₀ j hj ≫ (finiteExterior hπ data E₀ j hj).exteriorChart

instance finiteInitialChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteInitialChart hπ data j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The entire retained initial chart has the original ModificationX contraction. -/
@[reassoc] theorem finiteInitialChart_toCurve (j : ℕ) (hj : j ≤ n) :
    finiteInitialChart hπ data j hj ≫ finiteToCurve hπ data j hj =
      WeierstrassModificationX.toCurve W (π ^ start) (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
        (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [finiteInitialChart, Category.assoc, finiteExterior_toCurve, initialToCurve_exterior]
  rfl

/-- The retained initial chart has its original coefficient algebra structure. -/
@[reassoc] theorem finiteInitialChart_structure (j : ℕ) (hj : j ≤ n) :
    finiteInitialChart hπ data j hj ≫ finiteStructure hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R A₀)) := by
  rw [finiteStructure, finiteInitialChart_toCurve_assoc,
    WeierstrassModificationX.toCurve_structure]

variable (S : Type u) [CommRing S] [Algebra R S]
open scoped TensorProduct
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The actual initial tensor algebra, also at k=0, embeds in every finite base change. -/
def finiteInitialTensorChart (j : ℕ) (hj : j ≤ n) :
    Spec (.of (S ⊗[R] A₀)) ⟶ finiteTensorModel hπ data S j hj :=
  TensorOpenChart.chart _ _ (finiteInitialChart_structure hπ data j hj)

instance finiteInitialTensorChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteInitialTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (TensorOpenChart.chart _ _ _))

/-- The initial tensor algebra is the actual coefficient pullback of the retained initial chart. -/
theorem finiteInitialTensorChart_isPullback (j : ℕ) (hj : j ≤ n) :
    IsPullback (finiteInitialTensorChart hπ data S j hj) TensorOpenChart.projection
      (pullback.snd q (finiteStructure hπ data j hj)) (finiteInitialChart hπ data j hj) :=
  TensorOpenChart.chart_isPullback _ _ _

/-- The full original initial chart has exactly its retained preimage after base change. -/
theorem finiteInitialTensorChart_range (j : ℕ) (hj : j ≤ n) :
    Set.range (finiteInitialTensorChart hπ data S j hj) =
      (pullback.snd q (finiteStructure hπ data j hj)) ⁻¹'
        Set.range (finiteInitialChart hπ data j hj) :=
  TensorOpenChart.chart_range _ _ _

/-- The initial tensor chart retains its extended coefficient structure. -/
@[reassoc] theorem finiteInitialTensorChart_structure (j : ℕ) (hj : j ≤ n) :
    finiteInitialTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A₀))) :=
  TensorOpenChart.chart_fst _ _ _

/-- The initial tensor chart retains all its original cubic functions. -/
@[reassoc] theorem finiteInitialTensorChart_toCurve (j : ℕ) (hj : j ≤ n) :
    finiteInitialTensorChart hπ data S j hj ≫
      pullback.snd q (finiteStructure hπ data j hj) ≫ finiteToCurve hπ data j hj =
      TensorOpenChart.projection ≫
        WeierstrassModificationX.toCurve W (π ^ start) (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
          (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [← Category.assoc]
  change (TensorOpenChart.chart _ _ _ ≫ _) ≫ _ = _
  rw [TensorOpenChart.chart_snd, Category.assoc, finiteInitialChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
