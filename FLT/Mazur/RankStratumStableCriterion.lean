/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafStableSupportCriterion
public import FLT.Mazur.RankStratumRelativeClosedStabilization

/-!
# Relative higher-rank closedness is necessary for full stabilization

The sufficient condition used by the all-order original-scalar theorem
is also necessary. When higher frames fail relative closedness, every
pair of consecutive positive powers differs; a larger threshold cannot
repair this route to uniform compatible numerators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [IsNoetherian S] (n : ℕ)

/-- Full rank powers stabilize precisely when higher ranks are relatively closed. -/
theorem exists_rankStratum_stable_iff_next_relatively_closed :
    (∃ K : ℕ, ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
      rankStratumIdeal E n ^ (K + 1)) ↔
    IsClosed ((rankImageOpen E n).ι ⁻¹' (rankImageOpen E (n + 1) : Set S)) := by
  let _ : NoetherianSpace (rankImageOpen E n).toScheme :=
    NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : IsNoetherian (rankImageOpen E n).toScheme := ⟨⟩
  rw [IdealSheafClopenStabilization.exists_stable_iff_support_isOpen]
  change IsOpen ((rankImageOpen E n).ι ⁻¹' (rankImageOpen E (n + 1) : Set S)ᶜ) ↔ _
  rw [Set.preimage_compl, isOpen_compl_iff]

/-- Every positive rank-ideal power still changes when there is a genuine relative jump. -/
theorem rankStratum_pow_succ_ne_of_next_not_relatively_closed
    (hn : ¬ IsClosed ((rankImageOpen E n).ι ⁻¹'
      (rankImageOpen E (n + 1) : Set S))) (K : ℕ) :
    rankStratumIdeal E n ^ (K + 1 + 1) ≠ rankStratumIdeal E n ^ (K + 1) := by
  intro hK
  apply hn
  apply (exists_rankStratum_stable_iff_next_relatively_closed E n).mp
  exact ⟨K, IdealSheafClopenStabilization.powers_stable_of_succ_eq _ K hK⟩

end FLT.Mazur.RelativeOrderedTuples
