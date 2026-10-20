/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonFiberTorus
public import FLT.Mazur.WeierstrassSplitNodalProjectiveCoefficient
public import FLT.Mazur.WeierstrassProperCoefficientComposition

/-!
# The nodal torus retains the actual arithmetic coefficient projection

The entire torus parametrization commutes with coefficient change on the
zero-parameter cubic, including nonreduced tests and the identity section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ArithmeticOneGonNodalCoefficient

open OneGonSmoothing WeierstrassIntegralChart

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

/-- The entire zero-parameter equation is retained under coefficient change. -/
theorem equation_zero : (equation (0 : R)).map (algebraMap R A) = equation (0 : A) := by
  rw [equation_map, map_zero]

/-- The full nodal torus parametrization commutes with the original proper coefficient map. -/
@[reassoc] theorem torus_coefficient :
    Spec.map (CommRingCat.ofHom (nodalLaurentCoefficientMap (algebraMap R A))) ≫
        splitNodalTorusToCurve (-1 : Rˣ) =
      splitNodalTorusToCurve (-1 : Aˣ) ≫
        eqToHom (congrArg integralCurve (equation_zero R A).symm) ≫
          integralCoefficientMorphism (S := A) (equation (0 : R)) := by
  apply (cancel_mono (integralProjectiveMap (equation (0 : R)))).mp
  rw [Category.assoc, Category.assoc, Category.assoc, integralProjectiveMap_coefficient,
    integralProjectiveMap_congr_assoc _ _ (equation_zero R A).symm]
  exact splitNodalTorus_projectiveCoefficient (algebraMap R A) (-1 : Rˣ) (-1 : Aˣ)
    (by ext; simp)

end FLT.Mazur.ArithmeticOneGonNodalCoefficient
