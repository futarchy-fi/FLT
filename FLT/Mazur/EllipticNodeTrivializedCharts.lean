/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLaurentScale
public import FLT.Mazur.LaurentUnitScaledCoordinates

/-!
# Actual strict-depth charts in trivialized coordinates

Compose the original punctured branch immersions with explicit Laurent
coordinate substitutions. Evaluation at the arithmetic character recovers
the original proper specialization, with its unchanged coefficient maps.
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
  (j : ℕ) (hj : j ≤ n) (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
local notation "F" => ResidueField A
local notation "s" => nodeLaurentScale D r (start + j)
local notation "c" => terminalNodeChart hπ data D j hj hk0 (by omega) hp

/-- The original positive puncture in the explicitly scaled trivialized coordinate. -/
def nodeTrivializedPositiveChart : Spec (.of F[T;T⁻¹]) ⟶
    finiteGlobalTensorModel hπ data F j hj :=
  Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling s).toRingHom) ≫
    PolygonNodeBranches.right F ≫ c

/-- The original negative puncture in the explicitly scaled reciprocal coordinate. -/
def nodeTrivializedNegativeChart : Spec (.of F[T;T⁻¹]) ⟶
    finiteGlobalTensorModel hπ data F j hj :=
  Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-s)).toRingHom) ≫
    PolygonNodeBranches.left F ≫ c

variable (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (P : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
local notation "t" => nodeTrivializedParameter D c₆ h6 r P
local notation "pt" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := F) t)))

include hv in
/-- The positive trivialized chart reconstructs the entire original proper specialization. -/
theorem finitePointSpecialization_trivialized_positive (hb : v.b ∈ maximalIdeal A) :
    pt ≫ nodeTrivializedPositiveChart A hπ data D r j hj hk0 hp =
      finitePointSpecialization A hπ data j hj P := by
  have hu := node_positive_tangent_isUnit D v (by omega) (by omega) hb
  rw [nodeTrivializedPositiveChart, LaurentUnitPoints.spec_evalUnit_scaling_assoc]
  have he : Units.map (algebraMap F F) s * t = nodePositiveLaurentUnit A P v hu := by
    change s * t = _
    rw [← hv]
    exact (nodePositiveLaurentUnit_trivialized D c₆ h6 r v
      (by omega) (by omega) (Or.inr hb) hu).symm
  rw [he]
  exact (finitePointSpecialization_positive_laurent A hπ data D j hj hk0
    (by omega) hp P v hv hu).symm

include hv in
/-- A period root reconstructs the negative specialization by the reciprocal chart. -/
theorem finitePointSpecialization_trivialized_negative
    (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6) (hb : IsUnit v.b) :
    pt ≫ nodeTrivializedNegativeChart A hπ data D r j hj hk0 hp =
      finitePointSpecialization A hπ data j hj P := by
  rw [nodeTrivializedNegativeChart, LaurentUnitPoints.spec_evalUnit_reciprocal_assoc]
  have he : Units.map (algebraMap F F) (-s) / t = nodeNegativeLaurentUnit A P v hb := by
    change -s / t = _
    rw [← hv]
    exact (nodeNegativeLaurentUnit_trivialized D c₆ h6 r hr v
      (by omega) (by omega) hb).symm
  rw [he]
  exact (finitePointSpecialization_negative_laurent A hπ data D j hj hk0
    (by omega) hp P v hv hb).symm

end FLT.Mazur.WeierstrassDividedDepth
