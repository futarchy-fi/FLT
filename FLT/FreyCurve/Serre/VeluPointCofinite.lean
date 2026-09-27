/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSpecialization

/-!
# Cofinite sets of geometric points

Finite exceptional sets of abscissae give finite exceptional sets of curve points.
Over an algebraically closed characteristic-zero field, every abscissa occurs.
-/

@[expose] public section

namespace WeierstrassCurve.Velu
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- The extended abscissa map has finite fibers. -/
theorem finite_fiber_xCoord (x : K) :
    Set.Finite {P : E.toAffine.Point | xCoord P = x} := by
  apply ((Affine.finite_preimage_xRep0 (W := E.toAffine) x).union
    (Set.finite_singleton 0)).subset
  intro P hP
  cases P with
  | zero => exact Or.inr rfl
  | some u v h =>
    left
    change u = x at hP
    simpa only [Set.mem_ofPred_eq, Affine.Point.xRep_some, Matrix.cons_val_zero] using hP

/-- Pulling back a cofinite set of abscissae gives a cofinite set of points. -/
theorem tendsto_xCoord_cofinite :
    Filter.Tendsto (xCoord (E := E)) Filter.cofinite Filter.cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton (finite_fiber_xCoord E)

/-- Every abscissa occurs on an elliptic curve over an algebraically closed field. -/
theorem exists_nonsingular_ordinate [CharZero K] [IsAlgClosed K] [E.IsElliptic] (x : K) :
    ∃ y, E.toAffine.Nonsingular x y := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
    (4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆) (by decide : 0 < 2)
  refine ⟨(s - E.a₁ * x - E.a₃) / 2, Affine.equation_iff_nonsingular.mp ?_⟩
  rw [Affine.equation_iff]
  dsimp [b₂, b₄, b₆] at hs
  linear_combination hs / 4

/-- The geometric point group is infinite in characteristic zero. -/
theorem infinite_points [CharZero K] [IsAlgClosed K] [E.IsElliptic] :
    Infinite E.toAffine.Point := by
  apply Infinite.of_surjective (xCoord (E := E))
  intro x
  obtain ⟨y, hy⟩ := exists_nonsingular_ordinate E x
  exact ⟨.some x y hy, rfl⟩

end WeierstrassCurve.Velu
