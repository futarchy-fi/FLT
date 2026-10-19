/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSpectrumTests
public import FLT.Mazur.CyclicCharacteristicProductTestRestriction
public import FLT.Mazur.GeneralizedCurveBaseIsoEquivalence

/-!
# Full classification on arbitrary affine scheme tests

Spectrum coordinates preserve both the actual parameter map and its full
original-family comparison. The test's structure map is arbitrary.
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
variable {T V : Scheme} (t : T ⟶ Spec (.of
  (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U)))

/-- Changing test coordinates by an isomorphism preserves the actual parameter maps. -/
def productSpectrumTestMapEquiv (a : V ≅ T) :
    {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} ≃
    {k : V ⟶ productComparisonScheme n b c //
      k ≫ s = ((a.hom ≫ t) ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} where
  toFun k := ⟨a.hom ≫ k.val, by simp only [Category.assoc, k.property]⟩
  invFun k := ⟨a.inv ≫ k.val, by
    simp only [Category.assoc, k.property, Iso.inv_hom_id_assoc]⟩
  left_inv k := by apply Subtype.ext; simp
  right_inv k := by apply Subtype.ext; simp

/-- The full comparison commutes with any restriction of the test scheme. -/
theorem productSpectrumTestComparison_restrict (l : V ⟶ T)
    (k : {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c)
        (t ≫ L) (t ≫ R) l ((l ≫ t) ≫ L) ((l ≫ t) ≫ R)
        (Category.assoc _ _ _) (Category.assoc _ _ _)
        (productSpectrumTestComparison n b c U t k) =
      productSpectrumTestComparison n b c U (l ≫ t)
        ⟨l ≫ k.val, by simp only [Category.assoc, k.property]⟩ := by
  exact productUniversalComparisonOnTest_restrict n b c l (t ≫ L) (t ≫ R)
    ((l ≫ t) ≫ L) ((l ≫ t) ≫ R) (Category.assoc _ _ _) (Category.assoc _ _ _)
    k.val (productSpectrumTest_left n b c U t k) (productSpectrumTest_right n b c U t k)

variable [IsAffine T]

/-- Classification on an affine scheme uses its canonical spectrum isomorphism. -/
def productAffineSchemePointEquiv :
    {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} ≃
    ((normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :=
  (productSpectrumTestMapEquiv n b c U t T.isoSpec.symm).trans
    ((productSpectrumTestPointEquiv n b c U Γ(T, ⊤) (T.isoSpec.inv ≫ t)).trans
      (comparisonBaseIsoEquiv (normalizedCurve n b) (normalizedCurve n c)
        (t ≫ L) (t ≫ R) T.isoSpec.symm ((T.isoSpec.inv ≫ t) ≫ L)
        ((T.isoSpec.inv ≫ t) ≫ R) (Category.assoc _ _ _) (Category.assoc _ _ _)).symm)

/-- The affine scheme classifier recovers the actual universal full comparison. -/
theorem productAffineSchemePointEquiv_apply
    (k : {k : T ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι}) :
    productAffineSchemePointEquiv n b c U t k =
      productSpectrumTestComparison n b c U t k := by
  apply (comparisonBaseIsoEquiv (normalizedCurve n b) (normalizedCurve n c)
    (t ≫ L) (t ≫ R) T.isoSpec.symm ((T.isoSpec.inv ≫ t) ≫ L)
    ((T.isoSpec.inv ≫ t) ≫ R) (Category.assoc _ _ _) (Category.assoc _ _ _)).injective
  simp only [productAffineSchemePointEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    comparisonBaseIsoEquiv_apply]
  exact (productSpectrumTestComparison_restrict n b c U t T.isoSpec.inv k).symm

/-- Every original-family comparison on an arbitrary affine test has a unique parameter. -/
theorem productAffineSchemeComparison_unique
    (e : (normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :
    ∃! k : {k : T ⟶ productComparisonScheme n b c //
        k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι},
      productSpectrumTestComparison n b c U t k = e := by
  simpa only [← productAffineSchemePointEquiv_apply] using
    (productAffineSchemePointEquiv n b c U t).bijective.existsUnique e

end FLT.Mazur.CyclicCharacteristicAtlas
