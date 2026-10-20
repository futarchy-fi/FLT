/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankStratumThickenings
public import FLT.Mazur.IdealSheafSupportPower

/-!
# Geometric stabilization of a top rank stratum

If the next frame image is empty, the full rank stratum ideal on the current
image open is nilpotent. Noetherianity supplies one exponent on that whole
open, including every nilpotent coefficient. All later ideal powers agree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [IsNoetherian S] (n : ℕ)
  (hn : rankImageOpen E (n + 1) = ⊥)

include hn in
omit [AlgebraicGeometry.IsNoetherian S] in
/-- With no higher rank, the closed rank bound fills the entire current frame-image open. -/
theorem rankStratumClosed_eq_top_of_next_empty : rankStratumClosed E n = ⊤ := by
  ext x
  change (rankImageOpen E n).ι x ∈ rankAtMost E n ↔ True
  simp only [rankAtMost, hn, Opens.coe_bot, Set.mem_compl_iff,
    Set.mem_empty_iff_false, not_false_eq_true]

include hn in
omit [AlgebraicGeometry.IsNoetherian S] in
/-- The top rank ideal is the full nilradical, without a reducedness hypothesis. -/
theorem rankStratumIdeal_eq_nilradical_of_next_empty :
    rankStratumIdeal E n = (rankImageOpen E n).toScheme.nilradical := by
  rw [rankStratumIdeal, rankStratumClosed_eq_top_of_next_empty E n hn,
    Scheme.IdealSheafData.vanishingIdeal_top]

include hn in
/-- A single positive power of the actual top rank ideal vanishes on the whole open. -/
theorem exists_rankStratum_power_eq_bot_of_next_empty :
    ∃ K : ℕ, rankStratumIdeal E n ^ (K + 1) = ⊥ := by
  let _ : NoetherianSpace (rankImageOpen E n).toScheme :=
    NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : IsNoetherian (rankImageOpen E n).toScheme := ⟨⟩
  obtain ⟨K, hK⟩ := IdealSheafSupportPower.exists_pow_le (rankStratumIdeal E n) ⊥ (by
    rw [rankStratumIdeal_eq_nilradical_of_next_empty E n hn]
    exact le_rfl)
  exact ⟨K, le_antisymm hK bot_le⟩

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Nilpotence of the defining ideal stabilizes every subsequent order, with one threshold. -/
theorem rankStratum_powers_stable_of_eq_bot (K : ℕ)
    (hK : rankStratumIdeal E n ^ (K + 1) = ⊥) :
    ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
      rankStratumIdeal E n ^ (K + 1) := by
  intro l hl
  apply le_antisymm
  · exact fun U ↦ Ideal.pow_le_pow_right (Nat.succ_le_succ hl)
  · rw [hK]
    exact bot_le

include hn in
/-- Empty higher-frame image supplies genuine stabilization of the full scheme structures. -/
theorem exists_rankStratum_stable_of_next_empty :
    ∃ K : ℕ, ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
      rankStratumIdeal E n ^ (K + 1) := by
  obtain ⟨K, hK⟩ := exists_rankStratum_power_eq_bot_of_next_empty E n hn
  exact ⟨K, rankStratum_powers_stable_of_eq_bot E n K hK⟩

/-- The global finite rank bound constructs a rank with a stable full infinitesimal tail. -/
theorem exists_top_rank_stable [QuasiCompact E.hom] :
    ∃ n K : ℕ, rankImageOpen E (n + 1) = ⊥ ∧
      ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
        rankStratumIdeal E n ^ (K + 1) := by
  obtain ⟨n, hn⟩ := exists_empty_rank_image E
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_empty E n hn
  exact ⟨n, K, hn, hK⟩

end FLT.Mazur.RelativeOrderedTuples
