/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonBranchOrdinate

/-!
# Vanishing of the deeper common-scale ordinate

The mixed-depth bound leaves positive residual depth in both coefficient
quotients. At a closed-fiber point the common-scale deeper ordinate is zero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation IsLocalRing
set_option quotPrecheck false
variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
  [Algebra R S] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} {k l : ℕ}
  (e : Data W π l) (ee : CommonBranchData e k)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
  (hc : IsUnit (c (y W (π ^ l) e.b3 e.b4 e.b6) +
    algebraMap R S W.a₁ * c (x W (π ^ l) e.b3 e.b4 e.b6) + algebraMap R S e.b3))
  (ρ : S →ₐ[R] K)

/-- The denominator formula forces zero residue without an input ordinate assumption. -/
theorem commonBranchOrdinate_residue_zero
    (ht : algebraMap R K (π ^ (l - k)) = 0)
    (h4 : algebraMap R K ee.b4 = 0) (h6 : algebraMap R K ee.b6 = 0) :
    ρ (commonBranchOrdinate e ee c hc) = 0 := by
  simp only [map_pow] at ht
  simp only [commonBranchOrdinate, map_mul, map_add, map_pow, AlgHom.commutes,
    ht, h4, h6, zero_mul, zero_add]

variable [IsDomain R] [IsLocalRing R] {m : ℕ} (D : SplitNodeDepth W π m)

include D in
/-- Both common coefficient quotients vanish under the sum-middle bound. -/
theorem commonBranchData_residue_zero (hk : 0 < k) (hm : 2 * (k + l) ≤ m)
    (van : ∀ b ∈ maximalIdeal R, algebraMap R K b = 0) :
    algebraMap R K ee.b4 = 0 ∧ algebraMap R K ee.b6 = 0 := by
  constructor
  · exact van _ (Ideal.pow_le_self (by omega)
      (commonBranchData_b4_mem D e ee (by omega)))
  · exact van _ (Ideal.pow_le_self (by omega)
      (commonBranchData_b6_mem D e ee (by omega)))

include D in
/-- The deeper common-scale ordinate vanishes throughout the wider closed-fiber range. -/
theorem commonBranchOrdinate_node_residue_zero (hk : 0 < k) (hlt : k < l)
    (hm : 2 * (k + l) ≤ m)
    (van : ∀ b ∈ maximalIdeal R, algebraMap R K b = 0) :
    ρ (commonBranchOrdinate e ee c hc) = 0 := by
  obtain ⟨h4, h6⟩ := commonBranchData_residue_zero e ee D hk hm van
  have hp : algebraMap R K π = 0 :=
    van π (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  apply commonBranchOrdinate_residue_zero e ee c hc ρ _ h4 h6
  rw [map_pow, hp, zero_pow (by omega)]

end FLT.Mazur.WeierstrassDividedDepth
