/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TransferCochain
public import FLT.LocalClassFieldTheory.CocycleRectangle

/-!
# Changing the representatives in transfer

Every choice of left-coset representatives differs from the canonical choice
by a subgroup-valued function. The transferred cocycles differ by an explicit
one-cochain boundary.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  (H : Subgroup G) (k : G ⧸ H → H)

/-- Subgroup transport in the representatives `q.out * k q`. -/
def transferTransportUsing (g : G) (q : G ⧸ H) : H :=
  (k q)⁻¹ * transferTransport H g q * k (g⁻¹ • q)

/-- The changed transport really compares the changed representatives. -/
theorem transferTransportUsing_spec (g : G) (q : G ⧸ H) :
    (q.out * k q) * (transferTransportUsing H k g q : G) =
      g * ((g⁻¹ • q).out * k (g⁻¹ • q)) := by
  simp only [transferTransportUsing, Subgroup.coe_mul, Subgroup.coe_inv,
    mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc q.out, transferTransport_spec, mul_assoc]

/-- Any section of the coset projection has the stated form. -/
theorem exists_transferRepresentative_change (r : G ⧸ H → G)
    (hr : ∀ q, QuotientGroup.mk (r q) = q) :
    ∃ k : G ⧸ H → H, ∀ q, r q = q.out * k q := by
  let k : G ⧸ H → H := fun q => ⟨q.out⁻¹ * r q,
    QuotientGroup.eq.mp ((QuotientGroup.out_eq' q).trans (hr q).symm)⟩
  exact ⟨k, fun q => by simp [k]⟩

variable [Fintype (G ⧸ H)]

/-- The actual coset sum computed in the changed representatives. -/
def transferTwoUsing (c : H × H → M) (p : G × G) : M :=
  ∑ q : G ⧸ H, (q.out * k q) • c
    (transferTransportUsing H k p.1 q, transferTransportUsing H k p.2 (p.1⁻¹ • q))

/-- The explicit one-cochain measuring the change of representatives. -/
def transferRepresentativeHomotopy (c : H × H → M) (g : G) : M :=
  ∑ q : G ⧸ H, q.out •
    (c (k q, transferTransportUsing H k g q) -
      c (transferTransport H g q, k (g⁻¹ • q)))

/-- Changing representatives changes transfer by the displayed coboundary. -/
theorem transferTwoUsing_eq (c : H × H → M) (hc : IsCocycle₂ c) (g h : G) :
    transferTwoUsing H k c (g, h) = transferTwo H c (g, h) +
      (g • transferRepresentativeHomotopy H k c h -
        transferRepresentativeHomotopy H k c (g * h) +
          transferRepresentativeHomotopy H k c g) := by
  have he (q : G ⧸ H) := twoCocycle_rectangle c hc
    (transferTransport H g q) (transferTransport H h (g⁻¹ • q))
    (k q) (k (g⁻¹ • q)) (k (h⁻¹ • g⁻¹ • q))
  unfold transferTwoUsing
  simp only [mul_smul]
  change (∑ q : G ⧸ H, q.out • ((k q) • c
    (transferTransportUsing H k g q, transferTransportUsing H k h (g⁻¹ • q)))) = _
  simp only [transferTransportUsing, he, smul_add, smul_sub,
    transferTransport_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [transfer_sum_reindex H g (fun q => q.out •
    c (k q, (k q)⁻¹ * transferTransport H h q * k (h⁻¹ • q))),
    transfer_sum_reindex H g (fun q => q.out • c (transferTransport H h q, k (h⁻¹ • q)))]
  simp only [transferTwo, transferRepresentativeHomotopy, transferTransportUsing,
    transferTransport_mul, mul_inv_rev, mul_smul, Finset.sum_sub_distrib, smul_sub]
  abel

/-- Transfer in any changed representatives preserves the cocycle condition. -/
theorem transferTwoUsing_isCocycle (c : H × H → M) (hc : IsCocycle₂ c) :
    IsCocycle₂ (transferTwoUsing H k c) := by
  have he : transferTwoUsing H k c = correctTwoCocycle (transferTwo H c)
      (fun g => -transferRepresentativeHomotopy H k c g) := by
    funext p
    rw [transferTwoUsing_eq H k c hc p.1 p.2]
    simp only [correctTwoCocycle, smul_neg]
    abel
  rw [he]
  exact correctTwoCocycle_isCocycle _ (transferTwo_isCocycle H c hc) _

end LocalClassFieldTheory
