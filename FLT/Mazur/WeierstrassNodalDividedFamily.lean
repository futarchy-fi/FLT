/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalResidueTangentDepth

/-!
# The divided family constructed from original nonsplit nodal bounds

Choose the divided coefficients at every permitted depth directly from the
original maximal-ideal bounds. Their actual residue tangent equations have
vanishing linear coefficients, the correct scale, and the prescribed constant.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R}
  (hm : maximalIdeal R = Ideal.span {π}) {depth start n : ℕ}
  (hbound : 2 * (start + n) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)

omit [IsDomain R] in
/-- The whole finite divided family is constructed from the original coefficient bounds. -/
def nodalDepthFamily (i : Fin (n + 1)) : Data W π (start + i.val) :=
  (nodalDepth_exists_data hm (by omega : 2 * (start + i.val) ≤ depth) h3 h4 h6).some

local notation "d" => nodalDepthFamily hm hbound h3 h4 h6
local notation "Q" => AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))
local notation "q" => algebraMap R Q
variable (hπ : π ≠ 0)

include hπ in
/-- Every constructed member has both linear coefficients in the original maximal ideal. -/
theorem nodalDepthFamily_linear_mem (i : Fin (n + 1)) :
    (d i).b3 ∈ maximalIdeal R ∧ (d i).b4 ∈ maximalIdeal R :=
  nodalDepth_linear_mem hπ hm (d i) (by omega) h3 h4

include hπ in
/-- The same whole family has zero linear coefficients in the actual residue root algebra. -/
theorem nodalDepthFamily_tangent_linear_zero (i : Fin (n + 1)) :
    q (d i).b3 = 0 ∧ q (d i).b4 = 0 :=
  nodalDepth_tangent_linear_zero hπ hm (d i) (by omega) h3 h4

include hπ in
/-- Every interior family member has zero conic constant over the actual tangent algebra. -/
theorem nodalDepthFamily_tangent_constant_zero (i : Fin (n + 1)) (hi : i.val < n) :
    q (d i).b6 = 0 :=
  nodalDepth_tangent_constant_zero hπ hm (d i) (by omega) h6

omit [IsDomain R] in
/-- At exact terminal depth the constructed final conic has a unit constant. -/
theorem nodalDepthFamily_tangent_terminal_isUnit
    (heq : 2 * (start + n) = depth) (hnext : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) :
    IsUnit (q (d ⟨n, Nat.lt_succ_self n⟩).b6) :=
  nodalDepth_tangent_constant_isUnit hm (d ⟨n, Nat.lt_succ_self n⟩) heq hnext

omit [IsDomain R] in
include hm in
/-- Every positive-depth chart in the original family has zero incidence scale in Q. -/
theorem nodalDepthFamily_tangent_scale (i : Fin (n + 1)) (hi : 0 < start + i.val) :
    q (π ^ (start + i.val)) = 0 := nodalDepth_tangent_scale_zero hm hi

end FLT.Mazur.WeierstrassDividedDepth
