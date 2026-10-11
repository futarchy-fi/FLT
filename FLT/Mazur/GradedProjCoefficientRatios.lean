/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientGeneratorOpen
public import FLT.Mazur.ModuleSectionRatioOpen

/-!
# Ratios of the original coefficient sections

The intrinsic ratio on each generator subopen is the original homogeneous
fraction, as follows from evaluation in the original cocycle trivialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GradedProjLine
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The original coefficient ratio equals its homogeneous fraction on every chart subopen. -/
theorem coefficientSection_ratio (hd : 0 < d) (hcover : iSup (chart 𝒜 f) = ⊤)
    (i j : ι) (U : (Proj 𝒜).Opens) (hi : U ≤ chart 𝒜 f i) :
    sectionRatioOn (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i) U
        (by simpa only [coefficientSection_generatorOpen 𝒜 f hf hd hcover] using hi)
        (coefficientSection 𝒜 f hf j) =
      (Proj 𝒜).presheaf.map (homOfLE hi).op
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i j)) := by
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  apply ((cocycle 𝒜 f hf 1).evaluationEquiv i hi).injective
  change (cocycle 𝒜 f hf 1).evaluate i hi (_ • _) =
    (cocycle 𝒜 f hf 1).evaluate i hi _
  rw [ModuleSheafUnitCocycle.Cocycle.evaluate_smul,
    coefficientSection_evaluate_self, mul_one, coefficientSection_evaluate]

end FLT.Mazur.GradedProjLine
