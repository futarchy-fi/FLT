/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientComparisonNormalization

/-!
# Sealed local coefficient comparison maps

Keep the local section morphism behind a typed definition when substituting
large geometric schemes into the generic normalization theorem.
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
  {X : Scheme} (p : X ⟶ Proj 𝒜) (M : X.Modules) (t : ι → Γ(M, ⊤))

/-- The local comparison is the original pulled basis followed by the actual section map. -/
@[irreducible] def coefficientLocalHom (i : ι) :
    ((pullback p).obj (line 𝒜 f hf 1)).restrict (p ⁻¹ᵁ chart 𝒜 f i).ι ⟶
      M.restrict (p ⁻¹ᵁ chart 𝒜 f i).ι :=
  (modulePullbackTrivialization p (lineRestrictIso 𝒜 f hf 1 i)).hom ≫
    sectionHom M (p ⁻¹ᵁ chart 𝒜 f i) (M.presheaf.map (homOfLE le_top).op (t i))

/-- Unseal the actual local comparison only in a generic scheme context. -/
theorem coefficientLocalHom_eq (i : ι) :
    coefficientLocalHom 𝒜 f hf p M t i =
      (modulePullbackTrivialization p (lineRestrictIso 𝒜 f hf 1 i)).hom ≫
        sectionHom M (p ⁻¹ᵁ chart 𝒜 f i) (M.presheaf.map (homOfLE le_top).op (t i)) := by
  unfold coefficientLocalHom
  rfl

/-- Original section descent restricts to the sealed original local comparison. -/
theorem coefficientComparison_restrict_localHom
    (hcover : iSup (chart 𝒜 f) = ⊤)
    (ht : ∀ i, p ⁻¹ᵁ chart 𝒜 f i ≤ sectionGeneratorOpen M (t i))
    (hg : ∀ i j V hi hj, (((cocycle 𝒜 f hf 1).inverseImage p).unit i j V hi hj :
      Γ(X, V)) = sectionRatioOn M (t i) V (hi.trans (ht i)) (t j))
    (a : (pullback p).obj (line 𝒜 f hf 1) ⟶ M)
    (ha : a = ((cocycle 𝒜 f hf 1).pullbackIso p hcover).hom ≫
      (sectionCocycleIso M (fun i ↦ p ⁻¹ᵁ chart 𝒜 f i) t ht
        ((cocycle 𝒜 f hf 1).inverseImage p)
        (Cocycle.inverseImage_cover p hcover) hg).hom) (i : ι) :
    (restrictFunctor (p ⁻¹ᵁ chart 𝒜 f i).ι).map a =
      coefficientLocalHom 𝒜 f hf p M t i := by
  rw [coefficientLocalHom_eq]
  exact coefficientComparison_restrict 𝒜 f hf p hcover M t ht hg a ha i

end FLT.Mazur.GradedProjLine
