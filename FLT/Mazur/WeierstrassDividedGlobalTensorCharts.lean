/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorEmbedding
public import FLT.Mazur.WeierstrassDividedFiniteTensorGeometry

/-!
# Actual affine tensor charts in the global coefficient pullback

The divided and successive tensor algebras embed in the whole projective
model with their original contractions. These are the full affine charts.
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
  (S : Type u) [CommRing S] [Algebra R S]
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The original divided tensor algebra as an open in the global model. -/
def globalDividedTensorChart (j : ℕ) (hj : j ≤ n) :=
  finiteDividedTensorChart hπ data S j hj ≫ finiteLocalTensorEmbedding hπ data S j hj

/-- The original successive tensor algebra as an open in the global model. -/
def globalSuccessiveTensorChart (j : ℕ) (hj : j + 1 ≤ n) :=
  finiteSuccessiveTensorChart hπ data S j hj ≫
    finiteLocalTensorEmbedding hπ data S (j + 1) hj

instance globalDividedTensorChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (globalDividedTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance globalSuccessiveTensorChart_isOpenImmersion (j : ℕ) (hj : j + 1 ≤ n) :
    IsOpenImmersion (globalSuccessiveTensorChart hπ data S j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The global divided chart retains every original cubic function. -/
@[reassoc] theorem globalDividedTensorChart_toCurve (j : ℕ) (hj : j ≤ n) :
    globalDividedTensorChart hπ data S j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      TensorOpenChart.projection ≫ toCurve (data ⟨j, Nat.lt_succ_of_le hj⟩) := by
  rw [globalDividedTensorChart, Category.assoc, finiteLocalTensorEmbedding_toCurve,
    finiteDividedTensorChart_toCurve]

/-- The global successive chart retains its whole original cubic contraction. -/
@[reassoc] theorem globalSuccessiveTensorChart_toCurve (j : ℕ) (hj : j + 1 ≤ n) :
    globalSuccessiveTensorChart hπ data S j hj ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1) hj) ≫
        finiteGlobalContraction hπ data (j + 1) hj =
      TensorOpenChart.projection ≫
        xContraction hπ (data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩)
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) ≫
            toCurve (data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩) := by
  rw [globalSuccessiveTensorChart, Category.assoc, finiteLocalTensorEmbedding_toCurve,
    finiteSuccessiveTensorChart_toCurve]

/-- The full global divided chart keeps the extended coefficient structure. -/
@[reassoc] theorem globalDividedTensorChart_structure (j : ℕ) (hj : j ≤ n) :
    globalDividedTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
          (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
          (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 S))) := by
  rw [globalDividedTensorChart, Category.assoc, finiteLocalTensorEmbedding_structure,
    finiteDividedTensorChart_structure]

/-- The full global successive chart keeps the extended coefficient structure. -/
@[reassoc] theorem globalSuccessiveTensorChart_structure (j : ℕ) (hj : j + 1 ≤ n) :
    globalSuccessiveTensorChart hπ data S j hj ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S
        (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
          (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 S))) := by
  rw [globalSuccessiveTensorChart, Category.assoc, finiteLocalTensorEmbedding_structure,
    finiteSuccessiveTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
