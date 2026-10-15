/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteUnitEvaluation
public import FLT.Mazur.LaurentNormalizedReduction

/-!
# The actual original finite multiplication has the product closed reduction

The two already proved unit laws and the domain unit theorem compute the
closed reduction at every finite order. The possible error has coefficients
in the actual nilpotent reduction kernel; no infinitesimal equality is assumed.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K m
local notation "v" => completeIdentityFiniteMulUnit K n h i m

/-- At every order, the actual original unit reduces to the full product Laurent unit. -/
theorem completeIdentityFiniteMulUnit_reduction :
    Units.map (coeffMap (coeffMap (reduction K m).toRingHom)).toMonoidHom (v) =
      Units.map (LaurentPolynomial.C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹])
        (PolygonUniversalScaling.u (R := K)) * PolygonUniversalScaling.u :=
  LaurentNormalizedReduction.reduced_eq_product (reduction K m).toRingHom (v)
    (completeIdentityFiniteMulUnit_firstUnit K n h i m)
    (completeIdentityFiniteMulUnit_secondUnit K n h i m)

/-- The actual additive error from the product formula, with every nilpotent retained. -/
def completeIdentityFiniteMulDefect : (A)[T;T⁻¹][T;T⁻¹] :=
  (v : (A)[T;T⁻¹][T;T⁻¹]) -
    LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1

/-- The full additive multiplication error vanishes on the reduced coefficient fiber. -/
theorem completeIdentityFiniteMulDefect_reduction :
    coeffMap (coeffMap (reduction K m).toRingHom)
      (completeIdentityFiniteMulDefect K n h i m) = 0 := by
  have he := congrArg Units.val (completeIdentityFiniteMulUnit_reduction K n h i m)
  change coeffMap (coeffMap (reduction K m).toRingHom) (v : (A)[T;T⁻¹][T;T⁻¹]) = _
    at he
  rw [completeIdentityFiniteMulDefect, map_sub, he]
  simp [coeffMap_T, PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]

/-- Every coefficient of the original multiplication error has the exact stage nilpotence bound. -/
theorem completeIdentityFiniteMulDefect_coeff_pow (a b : ℤ) :
    ((completeIdentityFiniteMulDefect K n h i m).coeff a |>.coeff b) ^ (m + 1) = 0 := by
  apply reduction_kernel_pow
  change (reduction K m).toRingHom
    (((completeIdentityFiniteMulDefect K n h i m).coeff a).coeff b) = 0
  have he := congrArg (fun p : K[T;T⁻¹][T;T⁻¹] ↦ (p.coeff a).coeff b)
    (completeIdentityFiniteMulDefect_reduction K n h i m)
  simpa only [coeffMap_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using he

end FLT.Mazur.PolygonInfinitesimalStages
