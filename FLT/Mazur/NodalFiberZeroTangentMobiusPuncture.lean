/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberZeroTangentMobiusBoundary

/-!
# The full opposite puncture of the fractional zero-node chart

An evaluation for which the fractional coordinate is a specified unit
factors through the original polygon right branch with exactly that unit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.NodalFiber
set_option backward.isDefEq.respectTransparency false
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  (a : Rˣ) (ev : ZeroTangentOpen (a : R) →ₐ[R] B) (v : Bˣ)
  (hv : ev (zeroTangentFraction (a : R)) = (v : B))

include hv in
/-- The whole puncture has its exact fractional Laurent parameter. -/
@[reassoc] theorem zeroTangentMobiusChart_second_boundary :
    Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ zeroTangentMobiusChart a =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) v).toRingHom) ≫
        PolygonSmoothing.rightBranchOpen R 0 := by
  rw [zeroTangentMobiusChart_eq_spec, ← Spec.map_comp]
  exact PolygonSmoothing.boundary_rightBranchOpen 0
    (ev.comp (zeroTangentMobiusEvaluation a)) v (by
      change ev (zeroTangentMobiusEvaluation a (PolygonSmoothing.rightCoordinate 0)) = _
      rw [zeroTangentMobiusEvaluation_right, hv])

/-- Inverting a unit parameter is exactly postcomposition with the original edge inversion. -/
@[reassoc] theorem unitParameter_inverse :
    Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) v⁻¹).toRingHom) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := R) v).toRingHom) ≫
        (PolygonSmoothing.edgeInversion R).hom := by
  change _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  have h : LaurentUnitPoints.evalUnit (R := R) v⁻¹ =
      (LaurentUnitPoints.evalUnit v).comp LaurentPolynomial.invert.toAlgHom := by
    apply LaurentUnitPoints.hom_ext <;> simp
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f.toRingHom)) h

end FLT.Mazur.NodalFiber
