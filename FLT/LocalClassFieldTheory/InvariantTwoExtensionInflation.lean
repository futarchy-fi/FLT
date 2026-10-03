/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedInvariantSequence
public import FLT.LocalClassFieldTheory.GroupConnectingRestriction
public import FLT.LocalClassFieldTheory.OneCocycleInvariantSequence
public import FLT.LocalClassFieldTheory.TateTwoExtension

/-!
# Inflation of the divided invariant two-extension

The maps of the two concrete exact sequences prove the ordinary connecting
square. The subgroup-order factor occurs only on the scalar input, from the
proved divided projection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] (M : Rep.{0} ℤ G) (c : cocycles₂ M)
  (N : Subgroup G) [N.Normal] [Fintype N]
  (hQ : Limits.IsZero (tateCohomology (Rep.res N.subtype (shiftedCoefficients M)) 0))
  (hX : Limits.IsZero (tateCohomology (Rep.res N.subtype
    (oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c))) 0))

local notation "Q" => shiftedCoefficients M
local notation "b" => shiftedTwoCocycle M c
local notation "q" => QuotientGroup.mk' N
local notation "hC" => coinducedInvariantSequence_shortExact M N hQ
local notation "hD" => oneCocycleInvariantSequence_shortExact Q b N hX

/-- The ordinary operation of the actual divided invariant two-extension. -/
def invariantTwoExtensionCohomologyMap (n : ℕ) :
    groupCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) n ⟶
      groupCohomology (Rep.quotientToInvariants M N) (n + 2) :=
  groupCohomology.δ hD n (n + 1) rfl ≫
    groupCohomology.δ hC (n + 1) (n + 2) rfl

/-- Inflation of the invariant operation equals the original operation on the scaled input. -/
theorem invariantTwoExtension_inflation (n : ℕ) :
    invariantTwoExtensionCohomologyMap M c N hQ hX n ≫
      groupCohomology.map q (coinducedInvariantSequenceMap M N).τ₁ (n + 2) =
    groupCohomology.map q (oneCocycleInvariantSequenceMap Q b N hX).τ₃ n ≫
      twoExtensionCohomologyMap M c n := by
  have h₂ := groupConnecting_restriction q (coinducedInvariantSequenceMap M N)
    hC (coinducedCoefficientSequence_shortExact M) (n + 1)
  have h₁ := groupConnecting_restriction q (oneCocycleInvariantSequenceMap Q b N hX)
    hD (oneCocycleSequence_shortExact Q b) n
  change (groupCohomology.δ hD n (n + 1) rfl ≫
    groupCohomology.δ hC (n + 1) (n + 2) rfl) ≫ _ = _ ≫
      (groupCohomology.δ (oneCocycleSequence_shortExact Q b) n (n + 1) rfl ≫
        groupCohomology.δ (coinducedCoefficientSequence_shortExact M) (n + 1) (n + 2) rfl)
  rw [Category.assoc, h₂, ← Category.assoc]
  exact (congrArg (fun t => t ≫ groupCohomology.δ
    (coinducedCoefficientSequence_shortExact M) (n + 1) (n + 2) rfl) h₁).trans
      (Category.assoc _ _ _)

end LocalClassFieldTheory
