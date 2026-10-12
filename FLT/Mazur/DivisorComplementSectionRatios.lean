/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementCanonical
public import FLT.Mazur.TensorPowerGeneratorOpen
public import FLT.Mazur.DivisorSectionGeneratorOpen
public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# Canonical divisor ratios recover the original complement functions

The canonical tensor power is a generator away from the Cartier support.
Its projective section ratios are precisely the previously constructed pole
functions, with the actual open-section transport retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle
variable {X : Scheme} {I : X.IdealSheafData} (hI : EffectiveCartier I)
local notation "L" => divisorLineBundle I hI
local notation "U" => (I.support.compl : X.Opens)

/-- Every positive canonical power generates on the original Cartier complement. -/
theorem divisorComplement_le_powerGenerator (n : ℕ) (hn : 0 < n) :
    (U) ≤ sectionGeneratorOpen (tensorPower (L) n)
      (tensorPowerSection (L) ⊤ (divisorSection hI ⊤) n) := by
  rw [tensorPowerSection_generatorOpen hI.divisorLineBundle_locallyFreeRankOne _ hn,
    divisorSection_generatorOpen]

/-- Canonical-denominator ratios equal the original complement functions. -/
theorem divisorComplementFunction_eq_ratio (n : ℕ) (hn : 0 < n)
    (t : Γ(tensorPower (L) n, ⊤)) :
    divisorComplementFunction hI n t = (Scheme.Opens.topIso (X := X) (U)).inv
      (sectionRatioOn (tensorPower (L) n)
        (tensorPowerSection (L) ⊤ (divisorSection hI ⊤) n) (U)
        (divisorComplement_le_powerGenerator hI n hn) t) := by
  let d := tensorPowerSection (L) ⊤ (divisorSection hI ⊤) n
  have hw : (Scheme.Opens.ι (X := X) (U)) ''ᵁ ⊤ ≤ sectionGeneratorOpen (tensorPower (L) n) d :=
    (Scheme.Opens.ι_image_top (X := X) (U)).le.trans (divisorComplement_le_powerGenerator hI n hn)
  have he := congrArg
    (SectionGradedLocalCoordinates.coordinate (divisorComplementTrivialization hI) n ⊤)
    (sectionRatioOn_smul (tensorPower (L) n) d ((Scheme.Opens.ι (X := X) (U)) ''ᵁ ⊤) hw t)
  rw [SectionGradedLocalCoordinates.coordinate_smul] at he
  change (show Γ((Scheme.Opens.toScheme (X := X) (U)), ⊤) from
    sectionRatioOn (tensorPower (L) n) d ((Scheme.Opens.ι (X := X) (U)) ''ᵁ ⊤) hw t) *
      divisorComplementFunction hI n d = divisorComplementFunction hI n t at he
  rw [divisorComplementFunction_power, mul_one] at he
  rw [← he]
  exact (sectionRatioOn_restrict (tensorPower (L) n) d (U) ((Scheme.Opens.ι (X := X) (U)) ''ᵁ ⊤)
    (divisorComplement_le_powerGenerator hI n hn) (Scheme.Opens.ι_image_top (X := X) (U)).le t).symm

end FLT.Mazur.FCurve
