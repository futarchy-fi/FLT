/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteNodeLaurentSpecialization
public import FLT.Mazur.EllipticNodeMixedLaurentCharacter

/-!
# The actual proper specialization of a mixed-branch sum

The original Laurent unit of the output is the explicit quotient of the input
characters, with the coefficient factor a₁ cubed. Substituting it into the
original chart reconstructs the whole proper specialization morphism.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
local notation "F" => ResidueField A
local notation "α" => IsUnit.unit (IsUnit.map (residue A) (SplitNodeDepth.a₁_unit D))

/-- The actual output Laurent unit is an explicit quotient of the two original input units. -/
theorem node_add_first_unit_laurent_parameter
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (t : NodePointCoordinates A W π (P + Q))
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ depth / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b)
    (hpos : IsUnit (v.b + W.a₁ * v.a)) (hout : IsUnit t.b) :
    nodeNegativeLaurentUnit A (P + Q) t hout =
      (nodePositiveLaurentUnit A P v hpos)⁻¹ * (α ^ 3 * nodeNegativeLaurentUnit A Q w hd) := by
  apply (eq_inv_mul_iff_mul_eq).mpr
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, nodePositiveLaurentUnit_val,
    nodeNegativeLaurentUnit_val, IsUnit.unit_spec]
  exact node_add_first_unit_character D v w t hk hkw hw hb hd

variable (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n) (hj0 : 0 < start + j) (hjp : 2 * (start + j) < depth)

/-- The original proper specialization of the arithmetic sum has the computed Laurent parameter. -/
theorem finitePointSpecialization_mixed_sum_laurent
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (t : NodePointCoordinates A W π (P + Q)) (ht : t.depth = start + j)
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ depth / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b)
    (hpos : IsUnit (v.b + W.a₁ * v.a)) :
    finitePointSpecialization A hπ data j hj (P + Q) =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F)
        ((nodePositiveLaurentUnit A P v hpos)⁻¹ *
          (α ^ 3 * nodeNegativeLaurentUnit A Q w hd))).toRingHom) ≫
        PolygonNodeBranches.left F ≫ terminalNodeChart hπ data D j hj hj0 (by omega) hjp := by
  obtain ⟨t', _, _, hb'⟩ := exists_nodePointCoordinates_add_of_first_unit D v w hk hkw hw hb hd
  have hout : IsUnit t.b := (t.unique D.uniformizer_ne_zero D.maximalIdeal_eq t').2.2 ▸ hb'
  rw [finitePointSpecialization_negative_laurent A hπ data D j hj hj0 (by omega) hjp
    (P + Q) t ht hout, node_add_first_unit_laurent_parameter A D v w t hk hkw hw hb hd hpos hout]

end FLT.Mazur.WeierstrassDividedDepth
