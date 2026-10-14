/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeParameterTrivialization
public import FLT.Mazur.EllipticFiniteNodeLaurentSpecialization

/-!
# Original tangent units in trivialized coordinates

The Laurent chart scale retains the original a₁ and the specified period root.
Positive tangents are scaled coordinates; negative tangents are scaled
reciprocals. The latter scale is derived from the original period equation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing WeierstrassDividedDepth
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  (h6 : W.a₆ = π ^ n * c₆) (r : (ResidueField A)ˣ)
  {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The original tangent coefficient as a residue-field unit. -/
def nodeTangentUnit : (ResidueField A)ˣ := (D.a₁_unit.map (residue A)).unit

/-- This coefficient is the residue of the actual a₁, with no change of model. -/
@[simp] theorem nodeTangentUnit_val :
    (nodeTangentUnit D : ResidueField A) = residue A W.a₁ :=
  (D.a₁_unit.map (residue A)).unit_spec

/-- The original depth-k Laurent scale for a specified period root. -/
def nodeLaurentScale (k : ℕ) : (ResidueField A)ˣ := nodeTangentUnit D ^ 3 * r ^ k

/-- Positive original tangent coordinates have exactly the a₁-cubed denominator. -/
theorem nodePointParameterUnit_positive (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : v.depth ≤ n / 2)
    (hb : 2 * v.depth = n ∨ v.b ∈ maximalIdeal A)
    (hu : IsUnit (v.b + W.a₁ * v.a)) :
    nodePointParameterUnit D c₆ h6 P =
      nodePositiveLaurentUnit A P v hu / nodeTangentUnit D ^ 3 := by
  apply Units.ext
  simp only [nodePointParameterUnit_val, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, nodeTangentUnit_val, nodePositiveLaurentUnit_val]
  exact nodePointParameter_positive D c₆ v hv0 hv hb

/-- The positive tangent is recovered from the trivialized parameter by the original scale. -/
theorem nodePositiveLaurentUnit_trivialized (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : v.depth ≤ n / 2)
    (hb : 2 * v.depth = n ∨ v.b ∈ maximalIdeal A)
    (hu : IsUnit (v.b + W.a₁ * v.a)) :
    nodePositiveLaurentUnit A P v hu =
      nodeLaurentScale D r v.depth * nodeTrivializedParameter D c₆ h6 r P := by
  rw [nodeTrivializedParameter, nodePointLabel_val_positive D v hv hb,
    nodePointParameterUnit_positive D c₆ h6 v hv0 hv hb hu, nodeLaurentScale]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The strict negative original tangent retains exactly one original period. -/
theorem nodePointParameterUnit_negative (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hb : IsUnit v.b) :
    nodePointParameterUnit D c₆ h6 P =
      nodeWrapParameterUnit D c₆ h6 *
        (-(nodeTangentUnit D ^ 3) / nodeNegativeLaurentUnit A P v hb) := by
  apply Units.ext
  simp only [nodePointParameterUnit_val, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_neg, Units.val_pow_eq_pow_val, nodeTangentUnit_val,
    nodeNegativeLaurentUnit_val, nodeWrapParameterUnit_val]
  exact nodePointParameter_negative D c₆ v hv0 hv hb

/-- A genuine root makes the negative original tangent a scaled reciprocal coordinate. -/
theorem nodeNegativeLaurentUnit_trivialized
    (hr : r ^ n = nodeWrapParameterUnit D c₆ h6)
    (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hb : IsUnit v.b) :
    nodeNegativeLaurentUnit A P v hb =
      -nodeLaurentScale D r v.depth / nodeTrivializedParameter D c₆ h6 r P := by
  rw [nodeTrivializedParameter, nodePointLabel_val_negative D v hv0 hv hb,
    nodePointParameterUnit_negative D c₆ h6 v hv0 hv hb, ← hr, nodeLaurentScale]
  have hn : n = v.depth + (n - v.depth) := by omega
  rw [show r ^ n = r ^ v.depth * r ^ (n - v.depth) by
    conv_lhs => rw [hn, pow_add]]
  simp only [neg_mul, div_eq_mul_inv, mul_inv, inv_neg, inv_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

end FLT.Mazur
