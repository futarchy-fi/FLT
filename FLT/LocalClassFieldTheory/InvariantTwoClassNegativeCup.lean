/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.InvariantNegativeComposite
public import FLT.LocalClassFieldTheory.InvariantTwoExtensionInflation
public import FLT.LocalClassFieldTheory.TwoExtensionBoundaryCup

/-!
# The negative cup of the invariant two-class

The ordinary class of the two actual invariant sequences has negative cup
exactly equal to the unscaled descended ambient cup.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)
  (c : cocycles₂ M) (N : Subgroup G) [N.Normal] [Fintype N] [Fintype (G ⧸ N)]
  (hQ : Limits.IsZero (tateCohomology (Rep.res N.subtype (shiftedCoefficients M)) 0))
  (hX : Limits.IsZero (tateCohomology (Rep.res N.subtype
    (oneCocycleExtension (shiftedCoefficients M) (shiftedTwoCocycle M c))) 0))

local notation "C" => coinducedInvariantSequence M N
local notation "D" =>
  oneCocycleInvariantSequence (shiftedCoefficients M) (shiftedTwoCocycle M c) N hX
local notation "MQ" => Rep.quotientToInvariants M N
local notation "hC" => coinducedInvariantSequence_shortExact M N hQ
local notation "hD" => oneCocycleInvariantSequence_shortExact
  (shiftedCoefficients M) (shiftedTwoCocycle M c) N hX

omit [Fintype G] in
/-- The negative composite is cup by the ordinary class of the same two sequences. -/
theorem invariantNegativeComposite_eq_twoClassCup
    (x : tateCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) (-2)) :
    invariantNegativeComposite M c N hQ hX x =
      tateTwoClassMap MQ
        (invariantTwoExtensionCohomologyMap M c N hQ hX 0
          ((H0Iso (Rep.trivial ℤ (G ⧸ N) ℤ)).inv ⟨(1 : ℤ), fun _ => rfl⟩)) (-2) x := by
  exact twoExtension_boundary_negative_cup (C).X₁ (C).X₃ (C).X₂
    (C).f (C).g (C).zero hC (D).X₂ (D).f (D).g (D).zero hD x

/-- The invariant two-class has precisely the unscaled quotient negative cup. -/
theorem invariantTwoClassCup_eq_negativeCupQuotient
    (x : tateCohomology (Rep.trivial ℤ (G ⧸ N) ℤ) (-2)) :
    tateTwoClassMap MQ
      (invariantTwoExtensionCohomologyMap M c N hQ hX 0
        ((H0Iso (Rep.trivial ℤ (G ⧸ N) ℤ)).inv ⟨(1 : ℤ), fun _ => rfl⟩)) (-2) x =
      negativeCupQuotient M N (H2π M c) x := by
  rw [← invariantNegativeComposite_eq_twoClassCup]
  exact DFunLike.congr_fun (invariantNegativeComposite_eq_negativeCupQuotient M c N hQ hX) x

end LocalClassFieldTheory
