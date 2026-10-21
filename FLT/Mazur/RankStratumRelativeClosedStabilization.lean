/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStratumClopenStabilization

/-!
# Stabilization when higher ranks are closed only inside the current rank open

The higher-frame image need not be closed in the original source. It is
enough for its inverse image in the current rank-image open to be closed.
The full exact-rank ideal then stabilizes on that unchanged rank open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom] (n : ℕ)
  (hn : IsClosed ((rankImageOpen E n).ι ⁻¹' (rankImageOpen E (n + 1) : Set S)))

include hn in
/-- Relative closedness of higher ranks makes the exact-rank support open in its actual ambient. -/
theorem rankStratum_support_isOpen_of_next_relatively_closed :
    IsOpen ((rankStratumIdeal E n).support : Set (rankImageOpen E n).toScheme) := by
  change IsOpen ((rankImageOpen E n).ι ⁻¹' (rankImageOpen E (n + 1) : Set S)ᶜ)
  rw [Set.preimage_compl]
  exact hn.isOpen_compl

include hn in
/-- Full ideal powers stabilize even when the next frame image is not globally closed. -/
theorem exists_rankStratum_stable_of_next_relatively_closed [IsNoetherian S] :
    ∃ K : ℕ, ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
      rankStratumIdeal E n ^ (K + 1) := by
  let _ : NoetherianSpace (rankImageOpen E n).toScheme :=
    NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : IsNoetherian (rankImageOpen E n).toScheme := ⟨⟩
  exact IdealSheafClopenStabilization.exists_stable (rankStratumIdeal E n)
    (rankStratum_support_isOpen_of_next_relatively_closed E n hn)

end FLT.Mazur.RelativeOrderedTuples
