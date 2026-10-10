/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientSections
public import FLT.Mazur.OpenRestrictedScalarPullback
public import FLT.Mazur.ModuleCocycleChartSections

/-!
# Pullback of original chart coefficients

The original chart coefficient pulls back to its homogeneous fraction under
the actual scheme morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.GradedProjLine

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false



variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The original section's actual coefficient in its chosen chart trivialization. -/
def coefficientChartValue (i k : ι) : Γ((chart 𝒜 f i).toScheme, ⊤) :=
  (cocycle 𝒜 f hf 1).chartValue i (coefficientSection 𝒜 f hf k)

/-- The chosen chart coefficient is the original restricted homogeneous fraction. -/
theorem coefficientChartValue_eq (i k : ι) :
    coefficientChartValue 𝒜 f hf i k =
      (Proj 𝒜).presheaf.map (homOfLE ((chart 𝒜 f i).ι_image_le ⊤)).op
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k)) := by
  rw [coefficientChartValue, ModuleSheafUnitCocycle.Cocycle.chartValue_evaluate]
  exact coefficientSection_evaluate 𝒜 f hf i k _ _

/-- Chart coefficients pull back as the original homogeneous fractions. -/
theorem coefficientSection_chart_pullback {X : Scheme} (p : X ⟶ Proj 𝒜)
    (i k : ι) :
    (p ∣_ chart 𝒜 f i).appTop (coefficientChartValue 𝒜 f hf i k) =
      p.appLE (chart 𝒜 f i) ((p ⁻¹ᵁ chart 𝒜 f i).ι ''ᵁ ⊤)
        ((p ⁻¹ᵁ chart 𝒜 f i).ι_image_le ⊤)
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k)) := by
  rw [coefficientChartValue_eq]
  exact Approximation.morphismRestrict_top_restrict p (chart 𝒜 f i)
    (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k))

end FLT.Mazur.GradedProjLine
