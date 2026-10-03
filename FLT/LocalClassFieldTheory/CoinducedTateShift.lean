/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedTateAcyclic
public import FLT.LocalClassFieldTheory.TateTwoExtension

/-!
# Dimension shifting on the actual Tate complexes

The connecting map of the concrete coinduced sequence is an isomorphism in
every integer degree. Thus the second boundary in the two-extension cup is
already invertible, including at input degree minus two.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (M : Rep k G)

/-- The genuine coinduced connecting map is invertible in every Tate degree. -/
theorem coinducedTate_boundary_isIso (n : ℤ) :
    IsIso (TateCohomology.δ (coinducedCoefficientSequence_shortExact M) n) :=
  ShortComplex.SnakeInput.isIso_δ _ (coinducedTate_isZero M n)
    (coinducedTate_isZero M (n + 1))

/-- The dimension-shifting isomorphism has the actual boundary as its forward map. -/
def coinducedTateShift (n : ℤ) :
    tateCohomology (shiftedCoefficients M) n ≅ tateCohomology M (n + 1) := by
  letI := coinducedTate_boundary_isIso M n
  exact asIso (TateCohomology.δ (coinducedCoefficientSequence_shortExact M) n)

/-- The all-degree two-extension cup factors through the proved shift isomorphism. -/
theorem tateTwoExtensionMap_eq_shift (c : cocycles₂ M) (n : ℤ) :
    tateTwoExtensionMap M c n =
      TateCohomology.δ (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n ≫
        (coinducedTateShift M (n + 1)).hom ≫ eqToHom (by congr 1; omega) := rfl

/-- Surjectivity of the cup is equivalent to surjectivity of its first boundary. -/
theorem tateTwoExtensionMap_surjective_iff (c : cocycles₂ M) (n : ℤ) :
    Function.Surjective (tateTwoExtensionMap M c n).hom ↔
      Function.Surjective
        (TateCohomology.δ (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n).hom := by
  let e := coinducedTateShift M (n + 1) ≪≫ eqToIso (by congr 1; omega :
    tateCohomology M (n + 1 + 1) = tateCohomology M (n + 2))
  change Function.Surjective (e.toLinearEquiv ∘ _) ↔ _
  exact Function.Surjective.of_comp_iff' e.toLinearEquiv.bijective _

/-- Injectivity of the cup is equivalent to injectivity of its first boundary. -/
theorem tateTwoExtensionMap_injective_iff (c : cocycles₂ M) (n : ℤ) :
    Function.Injective (tateTwoExtensionMap M c n).hom ↔
      Function.Injective
        (TateCohomology.δ (oneCocycleSequence_shortExact _ (shiftedTwoCocycle M c)) n).hom := by
  let e := coinducedTateShift M (n + 1) ≪≫ eqToIso (by congr 1; omega :
    tateCohomology M (n + 1 + 1) = tateCohomology M (n + 2))
  change Function.Injective (e.toLinearEquiv ∘ _) ↔ _
  exact e.toLinearEquiv.injective.of_comp_iff _

end LocalClassFieldTheory
