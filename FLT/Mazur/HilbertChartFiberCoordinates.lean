/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartClassifyingMap
public import FLT.Mazur.HilbertChartBasisAlgebra

/-!
# Coordinates in an arbitrary scalar extension of a Hilbert chart

Multiplication, unit and generator coordinates in the actual chart fiber are
images of the universal parameters. These formulas apply to every chart point.
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient-ring instance for chart fibers. -/
local instance fiberCoordinatesCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart-ring instance for chart fibers. -/
local instance fiberCoordinatesChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- Multiplication of universal basis vectors recovers the defining table. -/
theorem basis_repr_mul (i j k : Fin d) :
    (basis R I d).repr (basis R I d i * basis R I d j) k = mulCoeff R I d i j k := by
  classical
  rw [basis_repr_coordinates, coordinates_mul]
  simp [coordinates_basis]

variable (S : Type*) [CommRing S] [Algebra (ChartRing R I d w) S]

/-- The actual fiber algebra at a chart point. -/
abbrev ChartFiber := S ⊗[ChartRing R I d w] ChartAlgebra R I d w

/-- The actual basis in the scalar extension of the chart family. -/
def fiberBasis : Module.Basis (Fin d) S (ChartFiber R I d w S) :=
  (chartBasis R I d w).baseChange S

/-- The universal ambient vectors in the actual fiber. -/
def fiberGenerator (i : I) : ChartFiber R I d w S :=
  1 ⊗ₜ chartInclusion R I d w (generator R I d i)

/-- Coordinates of an included vector commute with both scalar extensions. -/
theorem fiberBasis_repr_inclusion (a : UniversalAlgebra R I d) (k : Fin d) :
    (fiberBasis R I d w S).repr (1 ⊗ₜ chartInclusion R I d w a) k =
      algebraMap (ChartRing R I d w) S (chartMap R I d w ((basis R I d).repr a k)) := by
  rw [fiberBasis, Module.Basis.baseChange_repr_tmul, chartBasis_repr_inclusion,
    Algebra.smul_def, mul_one]

/-- The multiplication coordinates in every fiber are the mapped parameters. -/
theorem fiberBasis_mul (i j k : Fin d) :
    structureCoeff (A := ChartFiber R I d w S) (fiberBasis R I d w S) i j k =
      algebraMap (ChartRing R I d w) S (chartMap R I d w (mulCoeff R I d i j k)) := by
  change (fiberBasis R I d w S).repr
    (fiberBasis R I d w S i * fiberBasis R I d w S j) k = _
  simp only [fiberBasis, chartBasis, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  change (fiberBasis R I d w S).repr
    (1 ⊗ₜ chartInclusion R I d w (basis R I d i * basis R I d j)) k = _
  rw [fiberBasis_repr_inclusion, basis_repr_mul]

/-- The unit coordinates in every fiber are the mapped parameters. -/
theorem fiberBasis_unit (k : Fin d) :
    structureUnit (A := ChartFiber R I d w S) (fiberBasis R I d w S) k =
      algebraMap (ChartRing R I d w) S (chartMap R I d w (unitCoeff R I d k)) := by
  change (fiberBasis R I d w S).repr (1 ⊗ₜ (1 : ChartAlgebra R I d w)) k = _
  rw [← map_one (chartInclusion R I d w), fiberBasis_repr_inclusion,
    basis_repr_coordinates, coordinates_one]

/-- The generator coordinates in every fiber are the mapped parameters. -/
theorem fiberBasis_generator (i : I) (k : Fin d) :
    (fiberBasis R I d w S).repr (fiberGenerator R I d w S i) k =
      algebraMap (ChartRing R I d w) S (chartMap R I d w (generatorCoeff R I d i k)) := by
  rw [fiberGenerator, fiberBasis_repr_inclusion, basis_repr_coordinates]
  rfl

end FLT.Mazur.HilbertChart
