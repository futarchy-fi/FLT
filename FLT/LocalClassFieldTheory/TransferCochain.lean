/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TransferCoset
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Finite coset sums in degrees one and two

Transfer is defined using the actual subgroup transport and coefficient action.
The cocycle and boundary identities follow from transport multiplication and
reindexing the finite set of cosets.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open Finset groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Transfer of a one-cochain, as a finite coset sum. -/
def transferOne (b : H → M) (g : G) : M :=
  ∑ q : G ⧸ H, q.out • b (transferTransport H g q)

/-- Transfer of a two-cochain, as a finite coset sum. -/
def transferTwo (c : H × H → M) (p : G × G) : M :=
  ∑ q : G ⧸ H, q.out • c
    (transferTransport H p.1 q, transferTransport H p.2 (p.1⁻¹ • q))

/-- Reindex a coefficient sum by translation of cosets. -/
theorem transfer_sum_reindex (g : G) (f : G ⧸ H → M) :
    (∑ q : G ⧸ H, g • f (g⁻¹ • q)) = g • ∑ q : G ⧸ H, f q := by
  rw [← Finset.smul_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) f

omit [Fintype (G ⧸ H)] in
/-- The transport action on coefficients is the translated representative action. -/
theorem transferTransport_smul (g : G) (q : G ⧸ H) (m : M) :
    q.out • (transferTransport H g q • m) = g • ((g⁻¹ • q).out • m) := by
  change q.out • ((transferTransport H g q : G) • m) = _
  simp only [← mul_smul, transferTransport_spec]

/-- The finite coset sum sends actual two-cocycles to two-cocycles. -/
theorem transferTwo_isCocycle (c : H × H → M) (hc : IsCocycle₂ c) :
    IsCocycle₂ (transferTwo H c) := by
  intro g h j
  simp only [transferTwo, ← Finset.sum_add_distrib, mul_inv_rev, mul_smul,
    transferTransport_mul]
  calc
    _ = ∑ q : G ⧸ H, (g • ((g⁻¹ • q).out • c
        (transferTransport H h (g⁻¹ • q),
          transferTransport H j (h⁻¹ • g⁻¹ • q))) +
        q.out • c (transferTransport H g q,
          transferTransport H h (g⁻¹ • q) *
            transferTransport H j (h⁻¹ • g⁻¹ • q))) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [← smul_add, hc, smul_add, transferTransport_smul]
    _ = _ := by
      rw [Finset.sum_add_distrib, transfer_sum_reindex H g
        (fun q => q.out • c (transferTransport H h q, transferTransport H j (h⁻¹ • q)))]

/-- Transfer commutes with the one-cochain coboundary. -/
theorem transferTwo_boundary (b : H → M) (g h : G) :
    transferTwo H (fun p => p.1 • b p.2 - b (p.1 * p.2) + b p.1) (g, h) =
      g • transferOne H b h - transferOne H b (g * h) + transferOne H b g := by
  simp only [transferTwo, smul_add, smul_sub, transferTransport_smul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [transfer_sum_reindex H g (fun q => q.out • b (transferTransport H h q))]
  simp only [transferOne, transferTransport_mul]

/-- Every transferred two-coboundary is a two-coboundary. -/
theorem transferTwo_isCoboundary (c : H × H → M) (hc : IsCoboundary₂ c) :
    IsCoboundary₂ (transferTwo H c) := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨transferOne H b, fun g h => ?_⟩
  rw [← transferTwo_boundary]
  congr 1
  funext p
  exact hb p.1 p.2

end LocalClassFieldTheory
