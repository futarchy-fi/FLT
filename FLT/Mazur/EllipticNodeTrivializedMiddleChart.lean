/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedCharts
public import FLT.Mazur.EllipticFiniteMiddleLaurentCharacter

/-!
# The actual even-middle Laurent chart in trivialized coordinates

The original middle chart uses the vertical tangent. The period equation
identifies this coordinate with the same scaled reciprocal as the negative
branches, including the midpoint where the two arithmetic labels coincide.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (j : ℕ) (hj : j ≤ n) (hk0 : 0 < start + j) (hm : 2 * (start + j) = depth)
local notation "F" => ResidueField A
local notation "s" => nodeLaurentScale D r (start + j)

/-- The original middle torus with its explicit scaled reciprocal coordinate. -/
def nodeTrivializedMiddleChart : Spec (.of F[T;T⁻¹]) ⟶
    finiteGlobalTensorModel hπ data F j hj :=
  Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-s)).toRingHom) ≫
    terminalLaurentChart hπ data D j hj hk0 (by omega) hm

variable (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "t" => nodeTrivializedParameter D c₆ h6 r P
local notation "u" => finiteMiddleLaurentUnit A hπ data D j hj hk0 (by omega) hm P v hv

include hr in
/-- The original middle vertical unit is exactly the scaled reciprocal character. -/
theorem finiteMiddleLaurentUnit_trivialized : u = -s / t := by
  have hm' : 2 * v.depth = depth := by omega
  have hz : nodePointParameterUnit D c₆ h6 P =
      nodeWrapParameterUnit D c₆ h6 * (-(nodeTangentUnit D ^ 3) / u) := by
    apply Units.ext
    simp only [nodePointParameterUnit_val, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_neg, Units.val_pow_eq_pow_val, nodeTangentUnit_val,
      finiteMiddleLaurentUnit_val, nodeWrapParameterUnit_val]
    exact nodePointParameter_middle_negative D c₆ h6 v hm'
  rw [nodeTrivializedParameter, nodePointLabel_val_positive D v (by omega) (Or.inl hm'),
    hz, ← hr, nodeLaurentScale, hv]
  rw [show r ^ depth = r ^ (start + j) * r ^ (start + j) by
    conv_lhs => rw [← hm, two_mul, pow_add]]
  simp only [neg_mul, div_eq_mul_inv, mul_inv, inv_neg, inv_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

include hr v hv in
/-- Evaluating the middle chart at the character recovers the entire original specialization. -/
theorem finitePointSpecialization_trivialized_middle :
    Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F) t).toRingHom) ≫
        nodeTrivializedMiddleChart A hπ data D r j hj hk0 hm =
      finitePointSpecialization A hπ data j hj P := by
  rw [nodeTrivializedMiddleChart, LaurentUnitPoints.spec_evalUnit_reciprocal_assoc]
  have he : Units.map (algebraMap F F) (-s) / t = u := by
    change -s / t = _
    exact (finiteMiddleLaurentUnit_trivialized A hπ data D r j hj hk0 hm
      c₆ h6 hr P v hv).symm
  rw [he]
  exact (finitePointSpecialization_middle_character A hπ data D j hj hk0
    (by omega) hm P v hv).symm

end FLT.Mazur.WeierstrassDividedDepth
