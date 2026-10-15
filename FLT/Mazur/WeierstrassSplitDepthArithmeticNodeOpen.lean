/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticNodeOpen
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Arithmetic node opens forced by the original split-depth coefficients

Strictly interior depths supply all divisibilities needed to construct the
node open. The hypotheses concern the original equation and depth only.
The middle depth is deliberately excluded: its divided constant is a unit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (d : Data W π k)

omit [IsDomain R] in
include D in
/-- The original second coefficient is divisible by the original uniformizer. -/
theorem splitDepth_a2_dvd : π ∣ W.a₂ := by
  apply Ideal.mem_span_singleton.mp
  rw [← D.maximalIdeal_eq]
  exact D.a₂_mem

include D in
/-- Both divided linear coefficients retain a uniformizer at every bounded depth. -/
theorem splitDepth_linear_dvd (hk : 2 * k ≤ depth) : π ∣ d.b3 ∧ π ∣ d.b4 := by
  have h := WeierstrassDilatation.divided_linear_mem D k hk d.b3 d.b4
    d.factor3 d.factor4
  simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using h

include D in
/-- The divided constant retains a uniformizer strictly before the middle depth. -/
theorem splitDepth_constant_dvd (hk : 2 * k < depth) : π ∣ d.b6 := by
  have h := WeierstrassDilatation.divided_constant_mem D k hk d.b6 d.factor6
  simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using h

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} {depth start n : ℕ}
  (D : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hpos : 0 < start + j)
  (hdepth : 2 * (start + (j + 1)) < depth) (m : ℕ)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "Q" => PolygonArithmeticStages.Quotient R π m

/-- The actual arithmetic node open constructed from the split-depth datum alone. -/
def splitDepthArithmeticNodeChart :
    Spec (.of (PolygonSmoothing.ChartRing (PolygonArithmeticStages.parameter R π m))) ⟶
      finiteGlobalArithmeticStage D.uniformizer_ne_zero data (j + 1) hj m :=
  finiteArithmeticNodeChart D.uniformizer_ne_zero data j hj m D.a₁_unit
    (dvd_pow_self π (Nat.ne_of_gt hpos)) (splitDepth_a2_dvd D)
    (splitDepth_linear_dvd D d (Nat.le_of_lt hdepth)).1
    (splitDepth_linear_dvd D d (Nat.le_of_lt hdepth)).2
    (splitDepth_constant_dvd D d hdepth)

/-- The original interior split-depth comparison is an open immersion at every order. -/
theorem splitDepthArithmeticNodeChart_isOpenImmersion :
    IsOpenImmersion (splitDepthArithmeticNodeChart D data j hj hpos hdepth m) :=
  finiteArithmeticNodeChart_isOpenImmersion ..

/-- The constructed open preserves the actual arithmetic coefficient map. -/
@[reassoc] theorem splitDepthArithmeticNodeChart_structure :
    splitDepthArithmeticNodeChart D data j hj hpos hdepth m ≫
      finiteGlobalArithmeticStructure D.uniformizer_ne_zero data (j + 1) hj m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (PolygonSmoothing.ChartRing (PolygonArithmeticStages.parameter R π m)))) :=
  finiteArithmeticNodeChart_structure ..

/-- Its contraction retains the original cubic and the original quotient base. -/
@[reassoc] theorem splitDepthArithmeticNodeChart_toCubic_structure :
    splitDepthArithmeticNodeChart D data j hj hpos hdepth m ≫
      finiteGlobalArithmeticToCubic D.uniformizer_ne_zero data (j + 1) hj m ≫
        WeierstrassIntegralChart.integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap Q
        (PolygonSmoothing.ChartRing (PolygonArithmeticStages.parameter R π m)))) ≫
          PolygonArithmeticStages.baseToIntegral R π m :=
  finiteArithmeticNodeChart_toCubic_structure ..

end FLT.Mazur.WeierstrassDividedDepth
