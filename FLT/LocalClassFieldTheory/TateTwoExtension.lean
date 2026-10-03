/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CocycleDimensionShift
public import FLT.LocalClassFieldTheory.OneCocycleExtension
public import FLT.LocalClassFieldTheory.TateCocycleClass

/-!
# The Tate operation of a concrete two-extension

Splicing the coinduced coefficient sequence with the extension of the shifted
one-cocycle gives a degree-two operation on the actual Tate complexes. Both
connecting maps are defined in every integer degree. The ordinary degree-zero
operation sends `1` to the given two-class, fixing the normalization.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G) (c : cocycles₂ M)

/-- The ordinary degree-two operation of the constructed two-extension. -/
def twoExtensionCohomologyMap (n : ℕ) :
    groupCohomology (Rep.trivial k G k) n ⟶ groupCohomology M (n + 2) :=
  groupCohomology.δ (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n (n + 1) rfl ≫
    groupCohomology.δ (coinducedCoefficientSequence_shortExact M) (n + 1) (n + 2) rfl

/-- The concrete two-extension represents the supplied cohomology class. -/
theorem twoExtensionCohomologyMap_one :
    twoExtensionCohomologyMap M c 0
      ((H0Iso (Rep.trivial k G k)).inv ⟨(1 : k), fun _ => rfl⟩) = H2π M c := by
  exact (congrArg (groupCohomology.δ (coinducedCoefficientSequence_shortExact M) 1 2 rfl)
    (oneCocycle_connecting_one (shiftedCoefficients M) (shiftedTwoCocycle M c))).trans
      (shiftedTwoCocycle_connecting M c)

variable [Fintype G]

/-- The two-extension operation on actual Tate cohomology, in all integer degrees. -/
def tateTwoExtensionMap (n : ℤ) :
    tateCohomology (Rep.trivial k G k) n ⟶ tateCohomology M (n + 2) :=
  TateCohomology.δ (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n ≫
    TateCohomology.δ (coinducedCoefficientSequence_shortExact M) (n + 1) ≫
      eqToHom (by congr 1; omega)

/-- Evaluation of the all-degree map is the composite of the two genuine boundaries. -/
theorem tateTwoExtensionMap_apply (n : ℤ) (x : tateCohomology (Rep.trivial k G k) n) :
    tateTwoExtensionMap M c n x =
      (eqToHom (by congr 1; omega) : tateCohomology M (n + 1 + 1) ⟶
        tateCohomology M (n + 2))
        (TateCohomology.δ (coinducedCoefficientSequence_shortExact M) (n + 1)
          (TateCohomology.δ (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n x)) :=
  rfl

end LocalClassFieldTheory
