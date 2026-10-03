/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Coset coordinates for continuous transfer

The chosen representative of each left coset gives a subgroup-valued transport.
Its multiplication law supplies the arguments in the transfer of cochains.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable {G : Type*} [Group G] (H : Subgroup G)

/-- Transport from the coset `g⁻¹ • q` to `q`, expressed in the subgroup. -/
def transferTransport (g : G) (q : G ⧸ H) : H :=
  ⟨q.out⁻¹ * (g * (g⁻¹ • q).out), by
    apply QuotientGroup.eq.mp
    rw [QuotientGroup.out_eq', ← smul_eq_mul,
      MulAction.Quotient.mk_smul_out, smul_inv_smul]⟩

/-- The representative and transport multiply to the translated representative. -/
theorem transferTransport_spec (g : G) (q : G ⧸ H) :
    q.out * (transferTransport H g q : G) = g * (g⁻¹ • q).out := by
  simp [transferTransport]

/-- Transport respects multiplication, with the intermediate coset recorded. -/
theorem transferTransport_mul (g h : G) (q : G ⧸ H) :
    transferTransport H (g * h) q =
      transferTransport H g q * transferTransport H h (g⁻¹ • q) := by
  apply Subtype.ext
  simp [transferTransport, mul_inv_rev, mul_smul, mul_assoc]

/-- The identity has trivial subgroup transport. -/
@[simp] theorem transferTransport_one (q : G ⧸ H) : transferTransport H 1 q = 1 := by
  apply Subtype.ext
  simp [transferTransport]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Translation of a coset depends continuously on the group element. -/
theorem continuous_transferCoset (q : G ⧸ H) :
    Continuous (fun g : G => g⁻¹ • q) := by
  have he : (fun g : G => g⁻¹ • q) =
      fun g => (QuotientGroup.mk (g⁻¹ * q.out) : G ⧸ H) := by
    funext g
    exact (MulAction.Quotient.mk_smul_out H g⁻¹ q).symm
  rw [he]
  exact continuous_quotient_mk'.comp (continuous_inv.mul continuous_const)

/-- Chosen representatives vary continuously for an open subgroup. -/
theorem continuous_transferRepresentative (hH : IsOpen (H : Set G)) :
    Continuous (Quotient.out : G ⧸ H → G) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  exact continuous_of_discreteTopology

/-- Coset transport is continuous when the subgroup is open. -/
theorem continuous_transferTransport (hH : IsOpen (H : Set G)) (q : G ⧸ H) :
    Continuous (fun g => transferTransport H g q) := by
  exact (continuous_const.mul (continuous_id.mul
    ((continuous_transferRepresentative H hH).comp
      (continuous_transferCoset H q)))).subtype_mk _

end LocalClassFieldTheory
