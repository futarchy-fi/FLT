/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedSubgroup

/-!
# Coinduced acyclicity under an injective group map

Cosets of the image give coordinates for functions on the ambient group.
This avoids replacing an actual Galois restriction-of-scalars map by a
definitionally different subgroup inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G H : Type} [CommRing k] [Group G] [Group H]
  (M : Rep k G) (f : H →* G) (hf : Function.Injective f)

/-- Image cosets together with a source-group element parametrize the ambient group. -/
def injectiveCosetCoordinates : (G ⧸ f.range) × H ≃ G :=
  (Equiv.prodCongr (Equiv.refl _) (MonoidHom.ofInjective hf).toEquiv).trans
    (subgroupCosetCoordinates f.range)

/-- The restricted function module is coinduced from its coset-coordinate coefficients. -/
def coinducedInjectiveRestrictionIso : Rep.res f (coinducedCoefficients M) ≅
    coinducedCoefficients (Rep.trivial k H ((G ⧸ f.range) → M)) :=
  Rep.mkIso (.mk {
    toFun v h q := v (injectiveCosetCoordinates f hf (q, h))
    invFun v g := v ((injectiveCosetCoordinates f hf).symm g).2
      ((injectiveCosetCoordinates f hf).symm g).1
    left_inv v := by funext g; simp
    right_inv v := by funext h q; simp
    map_add' _ _ := rfl
    map_smul' _ _ := rfl } (fun g => by
      ext v h q
      change v ((q.out * f h) * f g) = v (q.out * f (h * g))
      rw [map_mul, mul_assoc]))

/-- Restriction preserves the original coefficient short exact sequence. -/
theorem coinducedInjectiveSequence_shortExact :
    ((coinducedCoefficientSequence M).map (Rep.resFunctor f)).ShortExact :=
  (Rep.shortExact_res f).mpr (coinducedCoefficientSequence_shortExact M)

variable [Fintype H]

include hf in
/-- Coinduced coefficients remain Tate acyclic under any injective finite group map. -/
theorem coinducedInjectiveRestriction_isZero (n : ℤ) :
    Limits.IsZero (tateCohomology (Rep.res f (coinducedCoefficients M)) n) :=
  (coinducedTate_isZero (Rep.trivial k H ((G ⧸ f.range) → M)) n).of_iso
    ((tateCohomologyFunctor n).mapIso (coinducedInjectiveRestrictionIso M f hf))

include hf in
/-- The original restricted coefficient boundary is invertible in every integer degree. -/
theorem coinducedInjective_boundary_isIso (n : ℤ) :
    IsIso (TateCohomology.δ (coinducedInjectiveSequence_shortExact M f) n) :=
  ShortComplex.SnakeInput.isIso_δ _ (coinducedInjectiveRestriction_isZero M f hf n)
    (coinducedInjectiveRestriction_isZero M f hf (n + 1))

end LocalClassFieldTheory
