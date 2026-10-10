/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalParameterComparison

/-!
# Laurent multiplication equals the classical split nodal point addition

The explicit unit parametrization respects addition, including infinity,
vertical pairs and characteristic two. The proof uses the proved inverse
parameter comparison and the existing classical nodal group law.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- The unit parametrization turns multiplication into the original projective addition. -/
theorem splitNodalUnitPoint_mul (s t : Kˣ) :
    splitNodalUnitPointEquiv a (s * t) =
      splitNodalUnitPointEquiv a s + splitNodalUnitPointEquiv a t := by
  classical
  apply (Point.toAffineAddEquiv (splitNodeCurve (a : K)).toProjective).injective
  apply splitNodeParameter_injective a.ne_zero
  change splitNodeParameter (a : K) (splitNodalUnitPointEquiv a (s * t)).toAffineLift =
    splitNodeParameter (a : K)
      (splitNodalUnitPointEquiv a s + splitNodalUnitPointEquiv a t).toAffineLift
  rw [Point.toAffineLift_add, splitNodeParameter_add,
    splitNodalUnitPoint_classical_parameter, splitNodalUnitPoint_classical_parameter,
    splitNodalUnitPoint_classical_parameter, Units.val_mul, mul_inv]

/-- The actual Laurent point parametrization is an additive equivalence from field units. -/
def splitNodalUnitPointAddEquiv : Additive Kˣ ≃+
    ((splitNodalEquation a).map (algebraMap K K)).toProjective.Point where
  toFun t := splitNodalUnitPointEquiv a t.toMul
  invFun P := Additive.ofMul ((splitNodalUnitPointEquiv a).symm P)
  left_inv := (splitNodalUnitPointEquiv a).left_inv
  right_inv := (splitNodalUnitPointEquiv a).right_inv
  map_add' := splitNodalUnitPoint_mul a

/-- The additive comparison has exactly the already constructed point parametrization. -/
theorem splitNodalUnitPointAddEquiv_apply (t : Kˣ) :
    splitNodalUnitPointAddEquiv a (Additive.ofMul t) = splitNodalUnitPointEquiv a t := rfl

/-- The inverse parametrization sends every classical sum to the product of its units. -/
theorem splitNodalUnitPoint_symm_add
    (P Q : ((splitNodalEquation a).map (algebraMap K K)).toProjective.Point) :
    (splitNodalUnitPointEquiv a).symm (P + Q) =
      (splitNodalUnitPointEquiv a).symm P * (splitNodalUnitPointEquiv a).symm Q := by
  apply (splitNodalUnitPointEquiv a).injective
  simp only [Equiv.apply_symm_apply, splitNodalUnitPoint_mul]

end FLT.Mazur.WeierstrassIntegralChart
