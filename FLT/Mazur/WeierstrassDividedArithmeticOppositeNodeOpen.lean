/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeNodeChart
public import FLT.Mazur.WeierstrassDividedArithmeticCoordinates
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassSplitDepthArithmeticNodeOpen

/-!
# Opposite arithmetic polygon node opens in the resolved global model

The opposite node branch is placed in the actual global arithmetic stage
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
local notation "c" => WeierstrassSuccessiveX.arithmeticOppositeNodeChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6

/-- The opposite original polygon node chart inside the actual resolved arithmetic thickening. -/
def finiteArithmeticOppositeNodeChart : Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
    finiteGlobalArithmeticStage hπ data (j + 1) hj m :=
  c ≫ Spec.map (CommRingCat.ofHom (e).toRingHom) ≫
    globalSuccessiveTensorChart hπ data Q j hj ≫
      (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom

/-- The opposite branch, including its inverse, is an actual open in the global stage. -/
theorem finiteArithmeticOppositeNodeChart_isOpenImmersion :
    IsOpenImmersion (finiteArithmeticOppositeNodeChart hπ data j hj m ha hs h2 h3 h4 h6) := by
  have hc := WeierstrassSuccessiveX.arithmeticOppositeNodeChart_isOpenImmersion π m W
    (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 h3 h4 h6
  have he : IsIso (CommRingCat.ofHom (e).toRingHom) :=
    (e).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold finiteArithmeticOppositeNodeChart
  infer_instance

/-- The opposite global node open retains the original arithmetic quotient coefficient structure. -/
@[reassoc] theorem finiteArithmeticOppositeNodeChart_structure :
    finiteArithmeticOppositeNodeChart hπ data j hj m ha hs h2 h3 h4 h6 ≫
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
    WeierstrassSuccessiveX.arithmeticOppositeNodeChart_structure]

/-- Contraction of the opposite node open preserves the original integral coefficients. -/
@[reassoc] theorem finiteArithmeticOppositeNodeChart_toCubic_structure :
    finiteArithmeticOppositeNodeChart hπ data j hj m ha hs h2 h3 h4 h6 ≫
      finiteGlobalArithmeticToCubic hπ data (j + 1) hj m ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom
        (algebraMap Q (PolygonSmoothing.ChartRing (parameter R π m)))) ≫ baseToIntegral R π m := by
  rw [finiteGlobalArithmeticToCubic_toBase, finiteArithmeticOppositeNodeChart_structure_assoc]

variable [IsLocalRing R] {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hpos : 0 < start + j) (hdepth : 2 * (start + (j + 1)) < depth)

/-- The opposite arithmetic node open is forced by the original interior split-depth data. -/
def splitDepthArithmeticOppositeNodeChart :
    Spec (.of (PolygonSmoothing.ChartRing (parameter R π m))) ⟶
      finiteGlobalArithmeticStage D.uniformizer_ne_zero data (j + 1) hj m :=
  finiteArithmeticOppositeNodeChart D.uniformizer_ne_zero data j hj m D.a₁_unit
    (dvd_pow_self π (Nat.ne_of_gt hpos)) (splitDepth_a2_dvd D)
    (splitDepth_linear_dvd D d (Nat.le_of_lt hdepth)).1
    (splitDepth_linear_dvd D d (Nat.le_of_lt hdepth)).2
    (splitDepth_constant_dvd D d hdepth)

/-- The opposite interior split-depth comparison is open at every arithmetic order. -/
theorem splitDepthArithmeticOppositeNodeChart_isOpenImmersion :
    IsOpenImmersion (splitDepthArithmeticOppositeNodeChart data j hj m D hpos hdepth) :=
  finiteArithmeticOppositeNodeChart_isOpenImmersion ..

/-- The opposite split-depth chart preserves the original quotient coefficient map. -/
@[reassoc] theorem splitDepthArithmeticOppositeNodeChart_structure :
    splitDepthArithmeticOppositeNodeChart data j hj m D hpos hdepth ≫
      finiteGlobalArithmeticStructure D.uniformizer_ne_zero data (j + 1) hj m =
        Spec.map (CommRingCat.ofHom
          (algebraMap Q (PolygonSmoothing.ChartRing (parameter R π m)))) :=
  finiteArithmeticOppositeNodeChart_structure ..

end FLT.Mazur.WeierstrassDividedDepth
