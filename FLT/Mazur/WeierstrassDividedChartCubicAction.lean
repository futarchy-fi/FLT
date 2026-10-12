/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteOriginalScaleOpen
public import FLT.Mazur.WeierstrassDividedGlobalPointAction
public import FLT.Mazur.WeierstrassDividedFiniteTensorCharts

/-!
# Regular original scale detects actions on the final divided chart

The final divided chart retains its entire original cubic map. An integral
cubic action square and a regular original uniformizer determine its actual
finite-model action, before any specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "orig" => WeierstrassDilatation.fromOriginal W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The final original divided chart as an open in the whole finite model. -/
def finiteDividedGlobalChart : chart d ⟶ finiteGlobalModel hπ data j hj :=
  (finiteExterior hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj).dividedChart ≫
    finiteLocalChart hπ data j hj

/-- The whole-model chart contracts to its exact original divided cubic map. -/
@[reassoc] theorem finiteDividedGlobalChart_cubic :
    finiteDividedGlobalChart hπ data j hj ≫ finiteGlobalContraction hπ data j hj =
      Spec.map (CommRingCat.ofHom (orig).toRingHom) ≫ integralCurveChart W 2 := by
  rw [finiteDividedGlobalChart, Category.assoc, finiteGlobal_divided_contraction]
  rfl

/-- The final original chart keeps precisely its coefficient algebra. -/
@[reassoc] theorem finiteDividedGlobalChart_structure :
    finiteDividedGlobalChart hπ data j hj ≫ finiteGlobalStructure hπ data j hj =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [finiteGlobalStructure, ← Category.assoc, finiteDividedGlobalChart_cubic]
  simp only [Category.assoc, integralCurveChart_structure, chartStructure,
    specAlgHom_structure]

variable {S : Type u} [CommRing S] [Algebra R S]
  (a : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (f g : WeierstrassDilatation.Coordinate W (π ^ (start + j))
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] S)
  (ha : a ≫ integralSmoothStructure W = Spec.map (CommRingCat.ofHom (algebraMap R S)))
local notation "c" => finiteDividedGlobalChart hπ data j hj

include ha in
/-- Every actual divided input keeps the smooth point's coefficient compatibility. -/
theorem finiteDividedGlobalChart_algebra_condition :
    a ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ c) ≫
        finiteGlobalStructure hπ data j hj := by
  rw [Category.assoc, finiteDividedGlobalChart_structure, specAlgHom_structure]
  exact ha

/-- A genuine cubic action square lifts uniquely when the original uniformizer is regular. -/
theorem finiteDividedGlobalChart_pointAction_of_cubic
    (hreg : IsRegular (algebraMap R S π))
    (hadd : Spec.map (CommRingCat.ofHom (g.comp orig).toRingHom) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W a
        (Spec.map (CommRingCat.ofHom (f.comp orig).toRingHom) ≫ integralCurveChart W 2)
        (by simp only [Category.assoc, integralCurveChart_structure, chartStructure,
          specAlgHom_structure]; exact ha)) :
    finiteGlobalPointAction hπ data j hj a
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ c)
      (finiteDividedGlobalChart_algebra_condition hπ data j hj a f ha) =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ c := by
  apply finiteGlobalContraction_ext_of_regular_scale hπ data j hj
    (g.comp orig).toRingHom (by simpa only [AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.commutes] using hreg)
  · simp only [finiteGlobalPointAction_contraction, Category.assoc,
      finiteDividedGlobalChart_cubic]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using hadd.symm
  · rw [Category.assoc, finiteDividedGlobalChart_cubic]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
