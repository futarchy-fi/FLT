/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentMobiusBoundary
public import FLT.Mazur.NodalFiberZeroTangentMobiusBoundary

/-!
# The arithmetic fractional construction specializes to the original zero-fiber chart

These are equalities on the entire localized algebras and full scheme charts.
The smoothing correction vanishes, leaving exactly the earlier normalization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (a : Rˣ)

/-- The full arithmetic forward map is precisely the existing zero-fiber map at zero. -/
theorem tangentMobiusForward_zero :
    tangentMobiusForward (0 : R) 0 a (by simp) = zeroTangentMobiusForward a := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (q (0 : R) + algebraMap R (Coordinate (0 : R)) (-1 : R)))
  apply hom_ext
  · change tangentMobiusForward 0 0 a _ (tangentP 0 (-1 : R)) =
      zeroTangentMobiusForward a (zeroTangentP (-1 : R))
    rw [tangentMobiusForward_p, zeroTangentMobiusForward_p, map_zero, add_zero]
    rfl
  · change tangentMobiusForward 0 0 a _ (tangentQ 0 (-1 : R)) =
      zeroTangentMobiusForward a (zeroTangentQ (-1 : R))
    rw [tangentMobiusForward_q, zeroTangentMobiusForward_q]
    rfl

/-- The full inverse coordinate equivalence specializes to the original zero-fiber equivalence. -/
theorem tangentMobiusEquiv_zero :
    tangentMobiusEquiv (0 : R) 0 a (by simp) = zeroTangentMobiusEquiv a := by
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun f ↦ f z) (tangentMobiusForward_zero a)

/-- Every polygon function has exactly its earlier zero-fiber pullback. -/
theorem tangentMobiusEvaluation_zero :
    tangentMobiusEvaluation (0 : R) 0 a (by simp) = zeroTangentMobiusEvaluation a := by
  unfold tangentMobiusEvaluation zeroTangentMobiusEvaluation
  rw [tangentMobiusForward_zero]

/-- The full arithmetic open immersion specializes to the actual original zero chart. -/
theorem tangentMobiusChart_zero :
    tangentMobiusChart (0 : R) 0 a (by simp) = zeroTangentMobiusChart a := by
  rw [tangentMobiusChart_eq_spec, zeroTangentMobiusChart_eq_spec, tangentMobiusEvaluation_zero]

end FLT.Mazur.NodalFiber
