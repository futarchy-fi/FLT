/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankStratumThickenings
public import FLT.Mazur.IdealSheafClopenStabilization

/-!
# Geometric stabilization below a closed higher-frame locus

The higher-frame image may be nonempty. If it is closed as well as open,
the exact rank has open closed support in the current rank-image open.
Noetherianity then stabilizes the full defining ideal powers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [IsNoetherian S] (n : ℕ)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- A closed higher-frame image makes the entire exact-rank closed support open. -/
theorem rankStratum_support_isOpen_of_next_closed
    (hn : IsClosed (rankImageOpen E (n + 1) : Set S)) :
    IsOpen ((rankStratumIdeal E n).support : Set (rankImageOpen E n).toScheme) := by
  change IsOpen ((rankImageOpen E n).ι ⁻¹' (rankImageOpen E (n + 1) : Set S)ᶜ)
  exact hn.isOpen_compl.preimage (rankImageOpen E n).ι.continuous

/-- Higher ranks can remain present while the actual full rank-ideal powers stabilize. -/
theorem exists_rankStratum_stable_of_next_closed
    (hn : IsClosed (rankImageOpen E (n + 1) : Set S)) :
    ∃ K : ℕ, ∀ l, K ≤ l → rankStratumIdeal E n ^ (l + 1) =
      rankStratumIdeal E n ^ (K + 1) := by
  let _ : NoetherianSpace (rankImageOpen E n).toScheme :=
    NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : IsNoetherian (rankImageOpen E n).toScheme := ⟨⟩
  exact IdealSheafClopenStabilization.exists_stable (rankStratumIdeal E n)
    (rankStratum_support_isOpen_of_next_closed E n hn)

end FLT.Mazur.RelativeOrderedTuples
