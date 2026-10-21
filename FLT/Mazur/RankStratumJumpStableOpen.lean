/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafStableOpenMaximal
public import FLT.Mazur.RelativeFrameRankJumpValuations
public import FLT.Mazur.RelativeRankStratumThickenings

/-!
# The exact open region for rank-power stabilization and its residual witnesses

Even when higher ranks are not relatively closed, the full rank ideal
stabilizes on a constructed dense open. Every omitted point has both an
actual nonextendible larger-frame valuation and nonstationary full powers
on every open neighborhood in the unchanged rank-image ambient. Density
is in that ambient; the stable open may miss the exact rank support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
namespace FLT.Mazur.RelativeOrderedTuples
open IdealSheafClopenStabilization
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom] (n : ℕ)

/-- The complement of the exact rank-support frontier, in the original rank-image open. -/
def rankPowerStableOpen : (rankImageOpen E n).toScheme.Opens :=
  stableOpen (rankStratumIdeal E n)

/-- This constructed rank region is dense without assuming closed higher ranks. -/
theorem rankPowerStableOpen_dense :
    Dense (rankPowerStableOpen E n : Set (rankImageOpen E n).toScheme) :=
  stableOpen_dense (rankStratumIdeal E n)

/-- Precisely the opens contained in this region have stationary pulled full rank powers. -/
theorem rankPowerStableOpen_characterization [IsNoetherian S]
    (U : (rankImageOpen E n).toScheme.Opens) :
    (∃ K : ℕ, ∀ l, K ≤ l → ((rankStratumIdeal E n).comap U.ι) ^ (l + 1) =
      ((rankStratumIdeal E n).comap U.ι) ^ (K + 1)) ↔ U ≤ rankPowerStableOpen E n := by
  let _ : NoetherianSpace (rankImageOpen E n).toScheme :=
    NoetherianSpace.set (rankImageOpen E n : Set S)
  let _ : IsNoetherian (rankImageOpen E n).toScheme := ⟨⟩
  exact exists_stable_on_open_iff _ U

/-- The exact full rank ideal stabilizes on the newly constructed dense open. -/
theorem exists_rankPowerStableOpen_stable [IsNoetherian S] :
    ∃ K : ℕ, ∀ l, K ≤ l →
      ((rankStratumIdeal E n).comap (rankPowerStableOpen E n).ι) ^ (l + 1) =
        ((rankStratumIdeal E n).comap (rankPowerStableOpen E n).ι) ^ (K + 1) :=
  (rankPowerStableOpen_characterization E n _).mpr le_rfl

/-- Every omitted rank point is the exact center of a nonextendible larger-frame valuation. -/
theorem exists_rankPowerJump_square [NoetherianSpace S]
    (x : (rankImageOpen E n).toScheme) (hx : x ∉ rankPowerStableOpen E n) :
    ∃ V : ValuativeCommSq (distinctScheme E (Fin (n + 1))).hom,
      V.i₂ (closedPoint V.R) = (rankImageOpen E n).ι x ∧ ¬ V.commSq.HasLift := by
  have hfront : x ∈ frontier ((rankStratumIdeal E n).support : Set _) := not_not.mp hx
  have hz := (rankStratumIdeal E n).support.isClosed.frontier_subset hfront
  have hc : x ∈ closure (((rankStratumIdeal E n).support : Set _)ᶜ) := by
    rw [frontier_eq_closure_inter_closure] at hfront
    exact hfront.2
  have hpre : closure (((rankStratumIdeal E n).support : Set _)ᶜ) ⊆
      (rankImageOpen E n).ι ⁻¹' closure (rankImageOpen E (n + 1) : Set S) := by
    apply closure_minimal _ (isClosed_closure.preimage (rankImageOpen E n).ι.continuous)
    intro y hy
    exact subset_closure (not_not.mp hy)
  exact exists_rankJump_square_no_lift E n ((rankImageOpen E n).ι x)
    ⟨x.property, hz⟩ (not_not.mpr (hpre hc))

/-- No larger threshold repairs full power stationarity on a neighborhood of an omitted point. -/
theorem rankPowerJump_pow_succ_ne [IsLocallyNoetherian S]
    (x : (rankImageOpen E n).toScheme) (hx : x ∉ rankPowerStableOpen E n)
    (U : (rankImageOpen E n).toScheme.Opens) (hU : x ∈ U) (K : ℕ) :
    ((rankStratumIdeal E n).comap U.ι) ^ (K + 1 + 1) ≠
      ((rankStratumIdeal E n).comap U.ι) ^ (K + 1) := by
  exact pow_succ_ne_on_neighborhood_of_frontier _ U x (not_not.mp hx) hU K

end FLT.Mazur.RelativeOrderedTuples
