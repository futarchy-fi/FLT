/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TransferCochain

/-!
# Restriction followed by transfer on two-cocycles

An explicit one-cochain witnesses that transfer of restriction differs from
multiplication by the number of cosets by a coboundary.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Finset groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  (H : Subgroup G)

/-- The summand of the homotopy comparing transfer-restriction with degree. -/
def transferRestrictionCorrection (c : G × G → M) (g : G) (q : G ⧸ H) : M :=
  c (q.out, transferTransport H g q) - c (g, (g⁻¹ • q).out)

/-- The cocycle identity gives the correction formula at each coset. -/
theorem transferRestrictionCorrection_identity (c : G × G → M) (hc : IsCocycle₂ c)
    (g h : G) (q : G ⧸ H) :
    q.out • c (transferTransport H g q, transferTransport H h (g⁻¹ • q)) =
      c (g, h) + g • transferRestrictionCorrection H c h (g⁻¹ • q) -
        transferRestrictionCorrection H c (g * h) q +
        transferRestrictionCorrection H c g q := by
  have h₁ := hc q.out (transferTransport H g q) (transferTransport H h (g⁻¹ • q))
  have h₂ := hc g (g⁻¹ • q).out (transferTransport H h (g⁻¹ • q))
  have h₃ := hc g h ((g * h)⁻¹ • q).out
  rw [transferTransport_spec] at h₁ h₂
  simp only [mul_inv_rev, mul_smul] at h₃
  simp only [transferRestrictionCorrection, transferTransport_mul, Subgroup.coe_mul,
    mul_inv_rev, mul_smul, smul_sub]
  rw [eq_sub_of_add_eq h₁.symm, eq_sub_of_add_eq h₂, eq_sub_of_add_eq' h₃.symm]
  abel

variable [Fintype (G ⧸ H)]

/-- The explicit one-cochain in the restriction-transfer homotopy. -/
def transferRestrictionHomotopy (c : G × G → M) (g : G) : M :=
  ∑ q : G ⧸ H, transferRestrictionCorrection H c g q

/-- Restriction followed by transfer is degree multiplication modulo a boundary. -/
theorem transferTwo_restriction (c : G × G → M) (hc : IsCocycle₂ c) (g h : G) :
    transferTwo H (fun p => c (p.1, p.2)) (g, h) =
      Fintype.card (G ⧸ H) • c (g, h) +
        (g • transferRestrictionHomotopy H c h -
          transferRestrictionHomotopy H c (g * h) + transferRestrictionHomotopy H c g) := by
  simp only [transferTwo, transferRestrictionCorrection_identity H c hc,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  rw [transfer_sum_reindex H g (fun q => transferRestrictionCorrection H c h q)]
  simp only [transferRestrictionHomotopy]
  abel

end LocalClassFieldTheory
