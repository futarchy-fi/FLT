/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorCoefficientSymmetry
public import FLT.Mazur.WeierstrassDividedCoefficientSymmetry
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedGlobalTensorInfinity

/-!
# The finite-model coefficient symmetry on its original tensor charts

The divided chart, successive chart, and infinity chart intertwine their
explicit coefficient tensor automorphisms with the same actual global
symmetry. The local-to-global atlas embedding also retains this operation.
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
  (S : Type u) [CommRing S] [Algebra R S] (e : S ≃ₐ[R] S)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "σ" => TensorCoefficientSymmetry.coefficient e
local notation "hσ" => TensorCoefficientSymmetry.coefficient_structure e

/-- The original full local-model embedding respects the coefficient operation. -/
@[reassoc] theorem finiteLocalTensorEmbedding_symmetry (j : ℕ) (hj : j ≤ n) :
    CartesianCoefficientSymmetry.map
      (IsPullback.of_hasPullback q (finiteStructure hπ data j hj)).flip σ hσ ≫
        finiteLocalTensorEmbedding hπ data S j hj =
      finiteLocalTensorEmbedding hπ data S j hj ≫
        finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ := by
  apply CartesianCoefficientSymmetry.map_naturality
    (IsPullback.of_hasPullback q (finiteStructure hπ data j hj)).flip σ hσ
    (IsPullback.of_hasPullback q (finiteGlobalStructure hπ data j hj)).flip
    (finiteLocalTensorEmbedding hπ data S j hj) (finiteLocalChart hπ data j hj)
  · exact finiteLocalTensorEmbedding_square hπ data S j hj
  · exact finiteLocalTensorEmbedding_structure hπ data S j hj

/-- The complete original divided chart has exactly the semilinear tensor operation. -/
@[reassoc] theorem globalDividedTensorChart_symmetry (j : ℕ) (hj : j ≤ n) :
    TensorCoefficientSymmetry.spectrum e ≫ globalDividedTensorChart hπ data S j hj =
      globalDividedTensorChart hπ data S j hj ≫
        finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ := by
  rw [globalDividedTensorChart, finiteDividedTensorChart,
    ← Category.assoc, TensorCoefficientSymmetry.chart_symmetry, Category.assoc,
    finiteLocalTensorEmbedding_symmetry, Category.assoc]

/-- The whole newest successive chart retains its original tensor coordinates. -/
@[reassoc] theorem globalSuccessiveTensorChart_symmetry (j : ℕ) (hj : j + 1 ≤ n) :
    TensorCoefficientSymmetry.spectrum e ≫ globalSuccessiveTensorChart hπ data S j hj =
      globalSuccessiveTensorChart hπ data S j hj ≫
        finiteGlobalCoefficientSymmetry hπ data (j + 1) hj S σ hσ := by
  rw [globalSuccessiveTensorChart, finiteSuccessiveTensorChart,
    ← Category.assoc, TensorCoefficientSymmetry.chart_symmetry, Category.assoc,
    finiteLocalTensorEmbedding_symmetry, Category.assoc]

/-- The original projective infinity chart is stable under the same global symmetry. -/
@[reassoc] theorem finiteInfinityTensorChart_symmetry (j : ℕ) (hj : j ≤ n) :
    TensorCoefficientSymmetry.spectrum e ≫ finiteInfinityTensorChart hπ data S j hj =
      finiteInfinityTensorChart hπ data S j hj ≫
        finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ :=
  TensorCoefficientSymmetry.chart_symmetry e _ _ _

end FLT.Mazur.WeierstrassDividedDepth
