/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductFullAffineClassification

/-!
# Full classification over arbitrary maps of spectra

The algebra structure on a spectrum test is recovered from its actual base
map. No algebra structure or compatibility with that map is an extra input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
  (U : (normalizedProduct n b c).affineOpens)
local notation "K" => DirectedAffineSpectrum.Ring (normalizedProduct n b c) U
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "s" => productComparisonStructure n b c
variable {T : Scheme} (t : T ⟶ Spec (.of
  (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U)))

/-- A test over the product chart preserves the left original base map. -/
theorem productSpectrumTest_left
    (k : {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    t ≫ L = k.val ≫ (s ≫ prod.fst) := by
  rw [← Category.assoc, k.property]
  simp only [productOpenLeft, DirectedAffineSpectrum.chart, Category.assoc]

/-- A test over the product chart preserves the right original base map. -/
theorem productSpectrumTest_right
    (k : {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    t ≫ R = k.val ≫ (s ≫ prod.snd) := by
  rw [← Category.assoc, k.property]
  simp only [productOpenRight, DirectedAffineSpectrum.chart, Category.assoc]

/-- The actual universal comparison evaluated over a specified spectrum chart. -/
def productSpectrumTestComparison
    (k : {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    (normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R) :=
  productUniversalComparisonOnTest n b c k.val (t ≫ L) (t ≫ R)
    (productSpectrumTest_left n b c U t k) (productSpectrumTest_right n b c U t k)

/-- Classification retains an independently specified map equal to the algebra map. -/
theorem productSpectrumTestComparison_unique_of_algebra (B : Type) [CommRing B]
    [Algebra K B] (t : Spec (.of B) ⟶ Spec (.of K))
    (ht : Spec.algebraMap K B = t)
    (e : (normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :
    ∃! k : {k : Spec (.of B) ⟶ productComparisonScheme n b c //
        k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι},
      productSpectrumTestComparison n b c U t k = e := by
  subst t
  exact productUniversalComparisonOnAffineTest_unique n b c U B e

/-- Every comparison over an arbitrary map of spectra has a unique actual parameter. -/
theorem productSpectrumTestComparison_unique (B : Type) [CommRing B]
    (t : Spec (.of B) ⟶ Spec (.of K))
    (e : (normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :
    ∃! k : {k : Spec (.of B) ⟶ productComparisonScheme n b c //
        k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι},
      productSpectrumTestComparison n b c U t k = e := by
  let _ : Algebra K B := (Spec.preimage t).hom.toAlgebra
  exact productSpectrumTestComparison_unique_of_algebra n b c U B t (Spec.map_preimage t) e

/-- Full classification for spectrum tests with their given, arbitrary base morphism. -/
def productSpectrumTestPointEquiv (B : Type) [CommRing B]
    (t : Spec (.of B) ⟶ Spec (.of K)) :
    {k : Spec (.of B) ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} ≃
    ((normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :=
  Equiv.ofBijective (productSpectrumTestComparison n b c U t)
    (by
      constructor
      · intro x y h
        obtain ⟨z, _, hz⟩ := productSpectrumTestComparison_unique n b c U B t
          (productSpectrumTestComparison n b c U t y)
        exact (hz x h).trans (hz y rfl).symm
      · intro e
        obtain ⟨k, hk, _⟩ := productSpectrumTestComparison_unique n b c U B t e
        exact ⟨k, hk⟩)

/-- This classification evaluates the actual global universal comparison. -/
theorem productSpectrumTestPointEquiv_apply (B : Type) [CommRing B]
    (t : Spec (.of B) ⟶ Spec (.of K))
    (k : {k : Spec (.of B) ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    productSpectrumTestPointEquiv n b c U B t k =
      productSpectrumTestComparison n b c U t k := rfl

end FLT.Mazur.CyclicCharacteristicAtlas
