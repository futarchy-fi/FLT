/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartBasisRelations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The actual algebra over a prescribed-basis chart

Base change the universal algebra to the quotient by the basis equations.
The base-changed basis proves finite freeness, and the prescribed polynomial
vectors become its actual basis vectors.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient-ring instance for nested tensor inference. -/
local instance basisAlgebraCoefficientsRing :
    CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart-ring instance for nested tensor inference. -/
local instance basisAlgebraChartRing :
    CommRing (ChartRing R I d w) := inferInstance

/-- The actual scalar extension to the closed basis chart. -/
abbrev ChartAlgebra := ChartRing R I d w ⊗[Coefficients R I d] UniversalAlgebra R I d

/-- The actual base-change map of universal algebras. -/
def chartInclusion : UniversalAlgebra R I d →ₐ[Coefficients R I d] ChartAlgebra R I d w :=
  Algebra.TensorProduct.includeRight

/-- The actual base-changed basis. -/
def chartBasis : Module.Basis (Fin d) (ChartRing R I d w) (ChartAlgebra R I d w) :=
  (basis R I d).baseChange (ChartRing R I d w)

instance : Module.Free (ChartRing R I d w) (ChartAlgebra R I d w) :=
  Module.Free.of_basis (chartBasis R I d w)

instance : Module.Finite (ChartRing R I d w) (ChartAlgebra R I d w) :=
  Module.Finite.of_basis (chartBasis R I d w)

/-- Coordinates of base-changed elements are reduced by the actual quotient map. -/
theorem chartBasis_repr_inclusion (a : UniversalAlgebra R I d) (k : Fin d) :
    (chartBasis R I d w).repr (chartInclusion R I d w a) k =
      chartMap R I d w ((basis R I d).repr a k) := by
  change ((basis R I d).baseChange (ChartRing R I d w)).repr (1 ⊗ₜ a) k = _
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

/-- The imposed equations identify each prescribed polynomial with its basis vector. -/
theorem chartInclusion_evaluation (i : Fin d) :
    chartInclusion R I d w (evaluation R I d (w i)) = chartBasis R I d w i := by
  apply (chartBasis R I d w).repr.injective
  ext k
  rw [chartBasis_repr_inclusion, chartMap_evaluation_repr, Module.Basis.repr_self_apply]

end FLT.Mazur.HilbertChart
