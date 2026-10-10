/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientSections
public import FLT.Mazur.ModuleSectionCocyclePullbackNormalization

/-!
# Local normalization with the coefficient line as source

Expose the cocycle calculation through the graded coefficient line, so
concrete geometric specializations keep the source sheaf sealed.
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

/-- A comparison factored by original section descent has its original local normalization. -/
theorem coefficientComparison_restrict {X : Scheme} (p : X ⟶ Proj 𝒜)
    (hcover : iSup (chart 𝒜 f) = ⊤) (M : X.Modules) (t : ι → Γ(M, ⊤))
    (ht : ∀ i, p ⁻¹ᵁ chart 𝒜 f i ≤ sectionGeneratorOpen M (t i))
    (hg : ∀ i j V hi hj, (((cocycle 𝒜 f hf 1).inverseImage p).unit i j V hi hj :
      Γ(X, V)) = sectionRatioOn M (t i) V (hi.trans (ht i)) (t j))
    (a : (pullback p).obj (line 𝒜 f hf 1) ⟶ M)
    (ha : a = ((cocycle 𝒜 f hf 1).pullbackIso p hcover).hom ≫
      (sectionCocycleIso M (fun i ↦ p ⁻¹ᵁ chart 𝒜 f i) t ht
        ((cocycle 𝒜 f hf 1).inverseImage p)
        (Cocycle.inverseImage_cover p hcover) hg).hom) (i : ι) :
    (restrictFunctor (p ⁻¹ᵁ chart 𝒜 f i).ι).map a =
      (modulePullbackTrivialization p (lineRestrictIso 𝒜 f hf 1 i)).hom ≫
        sectionHom M (p ⁻¹ᵁ chart 𝒜 f i) (M.presheaf.map (homOfLE le_top).op (t i)) := by
  rw [ha]
  exact sectionCocyclePullback_normalization (chart 𝒜 f) (cocycle 𝒜 f hf 1)
    hcover p M t ht hg i

end FLT.Mazur.GradedProjLine
