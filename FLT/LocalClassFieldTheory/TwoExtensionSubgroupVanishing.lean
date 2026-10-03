/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TwoExtensionRestriction
public import FLT.LocalClassFieldTheory.TateExactSequence

/-!
# Transporting twisted-extension vanishing to the original restricted sequence

The quotient comparison is already proved invertible on Tate cohomology.
Naturality therefore transports injectivity and surjectivity of the two
adjacent boundaries, and exactness kills the original restricted extension.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory CategoryTheory.Limits groupCohomology

variable {k G H : Type} [CommRing k] [Group G] [Group H] (M : Rep.{0} k G)
  (f : H →* G) (hf : Function.Injective f) [Fintype H] (c : cocycles₂ M)

local notation "Mr" => Rep.res f M
local notation "cr" => mapCocycles₂ f (𝟙 Mr) c
local notation "X" => oneCocycleSequence (shiftedCoefficients M) (shiftedTwoCocycle M c)
local notation "Y" => oneCocycleSequence (shiftedCoefficients Mr) (shiftedTwoCocycle Mr cr)
local notation "hX" => twoExtensionRestriction_shortExact M f c
local notation "hY" => oneCocycleSequence_shortExact (shiftedCoefficients Mr)
  (shiftedTwoCocycle Mr cr)

/-- The proved quotient comparison as an isomorphism of Tate groups. -/
def shiftedRestrictionTateIso (n : ℤ) :
    tateCohomology (Rep.res f (shiftedCoefficients M)) n ≅
      tateCohomology (shiftedCoefficients Mr) n := by
  letI := shiftedRestriction_isIso M f hf n
  exact asIso ((tateCohomologyFunctor n).map (shiftedRestriction M f))

include hf in
/-- The original restricted boundary is the subgroup boundary followed by the inverse comparison. -/
theorem twoExtensionSubgroup_boundary (n : ℤ) :
    TateCohomology.δ hX n = TateCohomology.δ hY n ≫
      (shiftedRestrictionTateIso M f hf (n + 1)).inv := by
  have := shiftedRestriction_isIso M f hf (n + 1)
  change TateCohomology.δ hX n = TateCohomology.δ hY n ≫
    inv ((tateCohomologyFunctor (n + 1)).map (shiftedRestriction M f))
  rw [← twoExtensionRestriction_boundary M f c n, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

include hf in
/-- Vanishing for the subgroup's constructed extension implies vanishing for the original one. -/
theorem twoExtensionSubgroup_isZero (n : ℤ)
    (h : Limits.IsZero (tateCohomology (Y).X₂ n)) :
    Limits.IsZero (tateCohomology (Rep.res f (X).X₂) n) := by
  have hm : Mono (TateCohomology.δ hY n) := ShortComplex.SnakeInput.mono_δ _ h
  have he : Epi (TateCohomology.δ hY (n - 1)) :=
    ShortComplex.SnakeInput.epi_δ _ (by
      change Limits.IsZero (tateCohomology (Y).X₂ (n - 1 + 1))
      simpa only [sub_add_cancel] using h)
  have := shiftedRestriction_isIso M f hf (n + 1)
  have := shiftedRestriction_isIso M f hf (n - 1 + 1)
  have hms : Mono (TateCohomology.δ hX n) := by
    rw [twoExtensionSubgroup_boundary M f hf]
    infer_instance
  have hes : Epi (TateCohomology.δ hX (n - 1)) := by
    rw [twoExtensionSubgroup_boundary M f hf]
    infer_instance
  apply (tateCohomology_exact₂ hX n).isZero_X₂
  · have hz : (tateCohomologyFunctor (n - 1 + 1)).map
        (((X).map (Rep.resFunctor f)).f) = 0 := by
      rw [← cancel_epi (TateCohomology.δ hX (n - 1)),
        TateCohomology.δ_map, comp_zero]
    have hn : n - 1 + 1 = n := by omega
    rw [hn] at hz
    exact hz
  · change (tateCohomologyFunctor n).map (((X).map (Rep.resFunctor f)).g) = 0
    rw [← cancel_mono (TateCohomology.δ hX n), TateCohomology.map_δ, zero_comp]

end LocalClassFieldTheory
