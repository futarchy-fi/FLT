/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteRetainedPointEquality
public import FLT.Mazur.EllipticFiniteNodeLaurentSpecialization

/-!
# Laurent characters determine the actual retained specialization

On each fixed strict-depth branch, equality of the original Laurent character
is equivalent to equality of the unrestricted proper specialization at every
later stage. These are the actual oriented parameters, not reassigned labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hp : 2 * (start + j) < depth)
  (P Q : (W.map (algebraMap A K)).toProjective.Point)
  (v : NodePointCoordinates A W π P) (hv : v.depth = start + j)
  (w : NodePointCoordinates A W π Q) (hw : w.depth = start + j)
local notation "F" => ResidueField A

include D hk0 hp hv in
/-- A negative primitive branch has zero residue on the opposite tangent. -/
theorem nodeNegativeLaurent_other_zero (hb : IsUnit v.b) :
    residue A (v.b + W.a₁ * v.a) = 0 := by
  apply (residue_eq_zero_iff _).mpr
  have h := (node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    depth v.depth (by omega) (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation).2
  exact h.elim (fun h => False.elim (h.1 hb)) (fun h => h.2)

include D hj hk0 hp hv hw

/-- On the negative branch the original vertical residue determines every later specialization. -/
theorem finitePointSpecialization_retained_negative_eq_iff
    (hvunit : IsUnit v.b) (hwunit : IsUnit w.b) :
    finitePointSpecialization A hπ data (j + 1 + r) hr P =
      finitePointSpecialization A hπ data (j + 1 + r) hr Q ↔
        residue A v.b = residue A w.b := by
  rw [finitePointSpecialization_retained_eq_iff A hπ data D j hj r hr hk0 hp P Q v hv w hw]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    have hP := nodeNegativeLaurent_other_zero A D j hk0 hp P v hv hvunit
    have hQ := nodeNegativeLaurent_other_zero A D j hk0 hp Q w hw hwunit
    rw [map_add, map_mul] at hP hQ
    apply mul_left_cancel₀ (D.a₁_unit.map (residue A)).ne_zero
    linear_combination hP - hQ - he

/-- On the positive branch the other tangent character determines every later specialization. -/
theorem finitePointSpecialization_retained_positive_eq_iff
    (hvzero : v.b ∈ maximalIdeal A) (hwzero : w.b ∈ maximalIdeal A) :
    finitePointSpecialization A hπ data (j + 1 + r) hr P =
      finitePointSpecialization A hπ data (j + 1 + r) hr Q ↔
        residue A (v.b + W.a₁ * v.a) = residue A (w.b + W.a₁ * w.a) := by
  rw [finitePointSpecialization_retained_eq_iff A hπ data D j hj r hr hk0 hp P Q v hv w hw]
  have hP : residue A v.b = 0 := (residue_eq_zero_iff _).mpr hvzero
  have hQ : residue A w.b = 0 := (residue_eq_zero_iff _).mpr hwzero
  constructor
  · rintro ⟨ha, hb⟩
    simp only [map_add, map_mul, ha, hb]
  · intro he
    rw [map_add, map_mul, map_add, map_mul, hP, hQ, zero_add, zero_add] at he
    exact ⟨mul_left_cancel₀ (D.a₁_unit.map (residue A)).ne_zero he, hP.trans hQ.symm⟩

/-- The unit-valued negative Laurent parameter detects equality in the actual retained model. -/
theorem finitePointSpecialization_retained_negative_unit_iff
    (hvunit : IsUnit v.b) (hwunit : IsUnit w.b) :
    finitePointSpecialization A hπ data (j + 1 + r) hr P =
      finitePointSpecialization A hπ data (j + 1 + r) hr Q ↔
        nodeNegativeLaurentUnit A P v hvunit = nodeNegativeLaurentUnit A Q w hwunit := by
  rw [finitePointSpecialization_retained_negative_eq_iff A hπ data D j hj r hr hk0 hp
    P Q v hv w hw hvunit hwunit]
  rw [← Units.val_inj, nodeNegativeLaurentUnit_val, nodeNegativeLaurentUnit_val]

end FLT.Mazur.WeierstrassDividedDepth
