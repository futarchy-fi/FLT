/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedSubgroup

/-!
# Dimension shifting for the restricted coefficient sequence

Restriction preserves the actual short exact sequence, and its middle module
is Tate acyclic on the subgroup. Its boundary is therefore invertible in every
integer degree, with no normality assumption on the subgroup.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)
  (H : Subgroup G)

/-- Restricting the concrete coefficient sequence preserves short exactness. -/
theorem coinducedSubgroupSequence_shortExact :
    ((coinducedCoefficientSequence M).map (Rep.resFunctor H.subtype)).ShortExact :=
  (Rep.shortExact_res H.subtype).mpr (coinducedCoefficientSequence_shortExact M)

variable [Fintype H]

/-- The boundary of the restricted coefficient sequence is an isomorphism. -/
theorem coinducedSubgroup_boundary_isIso (n : ℤ) :
    IsIso (TateCohomology.δ (coinducedSubgroupSequence_shortExact M H) n) :=
  ShortComplex.SnakeInput.isIso_δ _ (coinducedSubgroupTate_isZero M H n)
    (coinducedSubgroupTate_isZero M H (n + 1))

/-- The proved subgroup dimension shift uses the original coefficient quotient. -/
def coinducedSubgroupShift (n : ℤ) :
    tateCohomology (Rep.res H.subtype (shiftedCoefficients M)) n ≅
      tateCohomology (Rep.res H.subtype M) (n + 1) := by
  letI := coinducedSubgroup_boundary_isIso M H n
  exact asIso (TateCohomology.δ (coinducedSubgroupSequence_shortExact M H) n)

end LocalClassFieldTheory
