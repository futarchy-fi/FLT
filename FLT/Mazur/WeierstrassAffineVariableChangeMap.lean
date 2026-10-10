/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineProduct
public import FLT.Mazur.WeierstrassVariableChangeIntegralEquation

/-!
# Actual affine chart maps for integral admissible variable changes

The transported equation defines a coefficient-preserving algebra map on the
original normalized affine coordinate rings. Its two coordinate formulas are
proved over arbitrary rings, so normalization acts on actual affine schemes.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

include h in
/-- The transformed universal affine coordinates satisfy the original equation. -/
theorem affineVariableChange_equation :
    (W.map (algebraMap R (Coordinate V 2))).toAffine.Equation
      (algebraMap R _ (C.u : R) ^ 2 * coord V 2 0 + algebraMap R _ C.r)
      (algebraMap R _ (C.u : R) ^ 3 * coord V 2 1 +
        algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s * coord V 2 0 +
          algebraMap R _ C.t) := by
  apply (WeierstrassVariableChangeIntegralEquation.equation_iff
    (W.map (algebraMap R _)) (C.map (algebraMap R _)) _ _).mpr
  rw [map_variableChange, h]
  exact affine_equation_of_hom V (AlgHom.id R _)

/-- The actual contravariant map on normalized affine coordinate algebras. -/
def affineVariableChangeMap : Coordinate W 2 →ₐ[R] Coordinate V 2 :=
  evaluation W 2
    ![algebraMap R _ (C.u : R) ^ 2 * coord V 2 0 + algebraMap R _ C.r,
      algebraMap R _ (C.u : R) ^ 3 * coord V 2 1 +
        algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s * coord V 2 0 +
          algebraMap R _ C.t, 1]
    ((Projective.equation_some ..).mpr (affineVariableChange_equation W V C h)) rfl

/-- The affine scheme map retains the original abscissa transformation. -/
theorem affineVariableChangeMap_x :
    affineVariableChangeMap W V C h (coord W 2 0) =
      algebraMap R _ (C.u : R) ^ 2 * coord V 2 0 + algebraMap R _ C.r :=
  evaluation_coord _ _ _ _ _ _

/-- The affine scheme map retains the original ordinate transformation. -/
theorem affineVariableChangeMap_y :
    affineVariableChangeMap W V C h (coord W 2 1) =
      algebraMap R _ (C.u : R) ^ 3 * coord V 2 1 +
        algebraMap R _ (C.u : R) ^ 2 * algebraMap R _ C.s * coord V 2 0 +
          algebraMap R _ C.t := evaluation_coord _ _ _ _ _ _

end FLT.Mazur.WeierstrassIntegralChart
