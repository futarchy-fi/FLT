/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorTensorNumeratorComparison
public import FLT.Mazur.DivisorSectionGeneratorOpen
public import FLT.Mazur.ProperAmpleSectionExtension

/-!
# Exhaustion of an ample divisor complement over arbitrary affine bases

Every regular function has a numerator in an actual tensor power of the
original divisor line. The generator-open extension keeps the canonical
section and therefore recovers the original complement function exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback GlobalIdealPowerCompatibility
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] divisorLineBundle

variable {X S : Scheme} [IsAffine S] (f : X ⟶ S) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

include f in
/-- The original ample divisor complement is affine without a Noetherian base assumption. -/
theorem isAffineOpen_ampleDivisorComplement_unrestricted
    (hA : AmpleLineBundle (divisorLineBundle I hI)) : IsAffineOpen I.support.compl := by
  rw [← divisorSection_generatorOpen hI]
  exact hA.isAffineOpen_section_unrestricted f (divisorSection hI ⊤)

include f in
/-- Original divisor poles exhaust complement functions over an arbitrary proper affine base. -/
theorem exists_ampleDivisorComplementFunction_unrestricted
    (hA : AmpleLineBundle (divisorLineBundle I hI))
    (a : Γ((complement I).toScheme, ⊤)) :
    ∃ (m : ℕ) (t : Γ(tensorPower (divisorLineBundle I hI) m, ⊤)),
      divisorComplementFunction hI m t = a := by
  have hex := exists_ampleSection_numerator_unrestricted f hA (divisorSection hI ⊤)
  rw [divisorSection_generatorOpen hI] at hex
  obtain ⟨m, t, ht⟩ := hex ((complement I).topIso.hom a)
  erw [divisorSection_restrict] at ht
  refine ⟨m, t, (divisorComplementFunction_of_restrict hI m t _ ht).trans ?_⟩
  exact ConcreteCategory.congr_hom (complement I).topIso.hom_inv_id a

end FLT.Mazur.FCurve
