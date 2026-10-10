/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientComparisonCoherence
public import FLT.Mazur.ModulePullbackStageIso

/-!
# Coordinate detection with a sealed original stage comparison

The original comparison square can be specialized without expanding the component
isomorphisms of the pullback composition and equality comparisons.
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

/-- Original coordinate images determine the square with the sealed original comparison. -/
theorem coefficientSection_stage_coherence {X Z : Scheme}
    (p : X ⟶ Proj 𝒜) (q : Z ⟶ Proj 𝒜) (r : X ⟶ Z) (hpq : r ≫ q = p)
    (hcover : iSup (chart 𝒜 f) = ⊤) {M : X.Modules} {N : Z.Modules}
    (a : (pullback p).obj (line 𝒜 f hf 1) ⟶ M)
    (b : (pullback q).obj (line 𝒜 f hf 1) ⟶ N)
    (c : (pullback r).obj N ⟶ M)
    (hs : ∀ i, c.app ⊤ (pullGlobal r N
        (b.app ⊤ (pullGlobal q (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i)))) =
      a.app ⊤ (pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i))) :
    (pullback r).map b ≫ c =
      (pullbackStageIso p q r hpq (line 𝒜 f hf 1)).hom ≫ a := by
  rw [pullbackStageIso_hom, Category.assoc]
  exact coefficientSection_comparison_coherence 𝒜 f hf p q r hpq hcover a b c hs

end FLT.Mazur.GradedProjLine
