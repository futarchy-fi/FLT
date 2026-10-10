/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientChartPullback
public import FLT.Mazur.ModuleCocycleSectionImage
public import FLT.Mazur.GradedProjCoefficientLocalMap

/-!
# Transport of original coefficient sections from local normalization

The actual local coefficient formulas determine the global images of the
homogeneous coordinate sections on every covered pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.GradedProjLine

open FCurve ModuleSheafUnitCocycle

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- Local fraction normalization sends every pulled coordinate to its original section. -/
theorem coefficientSection_image {X : Scheme} (p : X ⟶ Proj 𝒜)
    (hcover : iSup (chart 𝒜 f) = ⊤) (M : X.Modules) (t : ι → Γ(M, ⊤))
    (ht : ∀ i, p ⁻¹ᵁ chart 𝒜 f i ≤ sectionGeneratorOpen M (t i))
    (a : (pullback p).obj (line 𝒜 f hf 1) ⟶ M)
    (ha : ∀ i, (restrictFunctor (p ⁻¹ᵁ chart 𝒜 f i).ι).map a =
      coefficientLocalHom 𝒜 f hf p M t i)
    (hr : ∀ i k V hV, p.appLE (chart 𝒜 f i) V hV
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i k)) =
      sectionRatioOn M (t i) V (hV.trans (ht i)) (t k)) (k : ι) :
    a.app ⊤ (pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf k)) = t k := by
  apply cocycleSection_image (cocycle 𝒜 f hf 1) p M t a
    (fun i ↦ (ha i).trans (coefficientLocalHom_eq 𝒜 f hf p M t i)) hcover
  intro i
  change (show Γ(X, (p ⁻¹ᵁ chart 𝒜 f i).ι ''ᵁ ⊤) from
    (p ∣_ chart 𝒜 f i).appTop (coefficientChartValue 𝒜 f hf i k)) •
      M.presheaf.map (homOfLE le_top).op (t i) = _
  rw [coefficientSection_chart_pullback, hr, sectionRatioOn_smul]

end FLT.Mazur.GradedProjLine
