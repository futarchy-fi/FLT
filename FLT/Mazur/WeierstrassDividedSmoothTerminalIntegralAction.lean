/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedChartCubicAction
public import FLT.Mazur.WeierstrassSmoothDividedIntegralOutput

/-!
# The actual terminal divided output is the finite integral action

The concrete secant source has a regular original uniformizer. Its exact
ordinary addition square therefore identifies the constructed divided output
with the genuine whole-model action, and the equality survives specialization.
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
local notation "T" => SmoothDividedSecantRing d
local notation "a" => smoothDividedSecantPoint d
local notation "f" => smoothDividedSecantInput d
local notation "g" => smoothDividedIntegralOutput d (IsRegular.of_ne_zero (pow_ne_zero _ hπ))
local notation "c" => finiteDividedGlobalChart hπ data j hj
local notation "orig" => WeierstrassDilatation.fromOriginal W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

omit [IsDomain R] [IsBezout R] in
/-- The concrete smooth point retains the coefficient structure of the secant algebra. -/
theorem smoothTerminalIntegralPoint_structure :
    a ≫ integralSmoothStructure W = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
  rw [smoothDividedSecant_structure]
  simp only [Category.assoc, integralCurveChart_structure, chartStructure,
    specAlgHom_structure]

omit [IsBezout R] in
/-- The constructed terminal output contracts to the exact original cubic sum. -/
theorem smoothTerminalIntegralOutput_cubic :
    Spec.map (CommRingCat.ofHom ((g).comp orig).toRingHom) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W a
        (Spec.map (CommRingCat.ofHom ((f).comp orig).toRingHom) ≫ integralCurveChart W 2)
        (by simp only [Category.assoc, integralCurveChart_structure, chartStructure,
          specAlgHom_structure]; exact smoothTerminalIntegralPoint_structure data j hj) := by
  simpa only [smoothDividedIntegralOutput_original, smoothDividedSecantInput_original,
    smoothDividedSecantPresentation, secantPairPresentation_right] using
    smoothDividedSecantOutput_addition d

/-- The original finite-model point action is exactly the constructed integral divided output. -/
theorem smoothTerminalIntegral_finitePointAction :
    finiteGlobalPointAction hπ data j hj a
      (Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c)
      (finiteDividedGlobalChart_algebra_condition hπ data j hj a f
        (smoothTerminalIntegralPoint_structure data j hj)) =
      Spec.map (CommRingCat.ofHom (g).toRingHom) ≫ c :=
  finiteDividedGlobalChart_pointAction_of_cubic hπ data j hj a f g
    (smoothTerminalIntegralPoint_structure data j hj)
    (smoothDividedSecant_base_regular d (IsRegular.of_ne_zero hπ))
    (smoothTerminalIntegralOutput_cubic hπ data j hj)

/-- The genuine integral action equality survives every residue specialization. -/
theorem smoothTerminalIntegral_finitePointAction_specialize {U : Scheme.{u}}
    (z : U ⟶ Spec (.of T)) :
    finiteGlobalPointAction hπ data j hj (z ≫ a)
      (z ≫ Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c)
      (by
        simpa only [Category.assoc] using
          congrArg (z ≫ ·) (finiteDividedGlobalChart_algebra_condition hπ data j hj a f
            (smoothTerminalIntegralPoint_structure data j hj))) =
      z ≫ Spec.map (CommRingCat.ofHom (g).toRingHom) ≫ c := by
  exact (finiteGlobalPointAction_comp hπ data j hj z a
    (Spec.map (CommRingCat.ofHom (f).toRingHom) ≫ c)
    (finiteDividedGlobalChart_algebra_condition hπ data j hj a f
      (smoothTerminalIntegralPoint_structure data j hj))).trans
        (congrArg (z ≫ ·) (smoothTerminalIntegral_finitePointAction hπ data j hj))

end FLT.Mazur.WeierstrassDividedDepth
