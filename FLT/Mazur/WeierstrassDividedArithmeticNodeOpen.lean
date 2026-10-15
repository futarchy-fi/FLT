/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticNodeChart
public import FLT.Mazur.WeierstrassDividedArithmeticCoordinates
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts

/-!
# Original arithmetic polygon node opens in the resolved global model

The constructed node branch is placed in the actual global arithmetic stage
through the existing full tensor chart. All coefficient maps are retained.
This is a local comparison, not a gluing of the entire polygon family.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (m : ℕ)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (h4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (h6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "e" => WeierstrassSuccessiveX.baseChangeEquiv W (π ^ (start + j)) π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) Q
local notation "c" => WeierstrassSuccessiveX.arithmeticNodeChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6

/-- The full original polygon node chart inside the actual resolved arithmetic thickening. -/
def finiteArithmeticNodeChart : Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
    finiteGlobalArithmeticStage hπ data (j + 1) hj m :=
  c ≫ Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
    globalSuccessiveTensorChart hπ data Q j hj ≫
      (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom

/-- The constructed branch, including its inverse, is an actual open in the global stage. -/
theorem finiteArithmeticNodeChart_isOpenImmersion :
    IsOpenImmersion (finiteArithmeticNodeChart hπ data j hj m ha hs h2 h3 h4 h6) := by
  have hc := WeierstrassSuccessiveX.arithmeticNodeChart_isOpenImmersion π m W
    (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6
  have he : IsIso (CommRingCat.ofHom (e).toRingHom) :=
    (e).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold finiteArithmeticNodeChart
  infer_instance

/-- The global node open retains the original arithmetic quotient coefficient structure. -/
@[reassoc] theorem finiteArithmeticNodeChart_structure :
    finiteArithmeticNodeChart hπ data j hj m ha hs h2 h3 h4 h6 ≫
      finiteGlobalArithmeticStructure hπ data (j + 1) hj m =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolygonSmoothing.ChartRing (parameter R π m)))) := by
  change (c ≫ Spec.map (CommRingCat.ofHom (e).toAlgHom.toRingHom) ≫
    globalSuccessiveTensorChart hπ data Q j hj ≫
      (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom) ≫
        pullback.snd (finiteGlobalStructure hπ data (j + 1) hj) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd,
    globalSuccessiveTensorChart_structure]
  rw [specAlgHom_structure (e).toAlgHom,
    WeierstrassSuccessiveX.arithmeticNodeChart_structure]

/-- Contraction of the constructed node open preserves the original integral coefficients. -/
@[reassoc] theorem finiteArithmeticNodeChart_toCubic_structure :
    finiteArithmeticNodeChart hπ data j hj m ha hs h2 h3 h4 h6 ≫
      finiteGlobalArithmeticToCubic hπ data (j + 1) hj m ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolygonSmoothing.ChartRing (parameter R π m)))) ≫ baseToIntegral R π m := by
  rw [finiteGlobalArithmeticToCubic_toBase, finiteArithmeticNodeChart_structure_assoc]

end FLT.Mazur.WeierstrassDividedDepth
