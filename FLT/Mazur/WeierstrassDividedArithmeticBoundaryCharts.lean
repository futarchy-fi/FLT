/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticCoordinates
public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts

/-!
# Original retained boundary charts in the arithmetic stage

The full initial and older successive tensor charts are placed in the actual
resolved arithmetic stage. Their original quotient coefficients are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))

/-- The full original initial tensor chart in every resolved arithmetic stage. -/
def finiteArithmeticInitialTensorChart (j : ℕ) (hj : j ≤ n) :
    Spec (.of (Q ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀))) ⟶
        finiteGlobalArithmeticStage hπ data j hj m :=
  globalInitialTensorChart hπ data Q j hj ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data j hj)).hom

/-- The initial arithmetic chart retains its full open immersion. -/
theorem finiteArithmeticInitialTensorChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteArithmeticInitialTensorChart hπ data m j hj) := by
  unfold finiteArithmeticInitialTensorChart
  infer_instance

/-- The initial arithmetic chart preserves the actual quotient coefficient map. -/
@[reassoc] theorem finiteArithmeticInitialTensorChart_structure (j : ℕ) (hj : j ≤ n) :
    finiteArithmeticInitialTensorChart hπ data m j hj ≫
      finiteGlobalArithmeticStructure hπ data j hj m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (Q ⊗[R] WeierstrassModificationX.Coordinate W (π ^ start)
            (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)))) := by
  change (globalInitialTensorChart hπ data Q j hj ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data j hj)).hom) ≫
      pullback.snd (finiteGlobalStructure hπ data j hj) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, globalInitialTensorChart_structure]

variable (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

/-- An original older successive tensor chart in its actual later arithmetic stage. -/
def finiteArithmeticOlderTensorChart :
    Spec (.of (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q)) ⟶
        finiteGlobalArithmeticStage hπ data (j + 1 + r) hr m :=
  olderGlobalTensorChart hπ data Q j hj r hr ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1 + r) hr)).hom

/-- Retention preserves the full older arithmetic open immersion. -/
theorem finiteArithmeticOlderTensorChart_isOpenImmersion :
    IsOpenImmersion (finiteArithmeticOlderTensorChart hπ data m j hj r hr) := by
  unfold finiteArithmeticOlderTensorChart
  infer_instance

/-- Every older arithmetic chart retains the original quotient coefficient morphism. -/
@[reassoc] theorem finiteArithmeticOlderTensorChart_structure :
    finiteArithmeticOlderTensorChart hπ data m j hj r hr ≫
      finiteGlobalArithmeticStructure hπ data (j + 1 + r) hr m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (WeierstrassSuccessiveX.ScalarExtension W (π ^ (start + j)) π
            (Data.b3 e) (Data.b4 e) (Data.b6 e) Q))) := by
  change (olderGlobalTensorChart hπ data Q j hj r hr ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1 + r) hr)).hom) ≫
      pullback.snd (finiteGlobalStructure hπ data (j + 1 + r) hr) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, olderGlobalTensorChart_structure]

end FLT.Mazur.WeierstrassDividedDepth
