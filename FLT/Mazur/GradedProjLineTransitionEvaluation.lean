/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineSheaf
public import FLT.Mazur.ModuleUnitCocyclePullback

/-!
# Evaluating the coefficient-line transitions on one chart

The coefficient transition on an overlap is restriction of the ordinary
homogeneous coordinate ratio from its denominator chart. The same identity
computes its pullback along any scheme morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.GradedProjLine

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- An overlap transition is the restriction of the denominator-chart coordinate. -/
theorem coefficient_unit_eq (i j : ι) (V : (Proj 𝒜).Opens)
    (hi : V ≤ chart 𝒜 f i) (hj : V ≤ chart 𝒜 f j) :
    ((cocycle 𝒜 f hf 1).unit i j V hi hj : Γ(Proj 𝒜, V)) =
      (Proj 𝒜).presheaf.map (homOfLE hi).op
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i j)) := by
  change (Proj 𝒜).presheaf.map _
    ((twistTransition 𝒜 f hf 1 i j : Γ(Proj 𝒜, chart 𝒜 f i ⊓ chart 𝒜 f j))) = _
  simp only [twistTransition, restrictUnits, transitionSection, transitionUnit, zpow_one,
    Units.coe_map, ratioUnit_val]
  have he := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection 𝒜 (hf j) (f := f i) rfl) (coordinate 𝒜 f hf i j)
  change Proj.awayToSection 𝒜 (f i * f j)
    (toOverlap 𝒜 f hf i j (coordinate 𝒜 f hf i j)) = _ at he
  erw [he]
  rfl

/-- Pullback transitions are computed directly on the denominator chart. -/
theorem coefficient_inverseImage_unit {X : Scheme} (p : X ⟶ Proj 𝒜)
    (i j : ι) (V : X.Opens) (hi : V ≤ p ⁻¹ᵁ chart 𝒜 f i)
    (hj : V ≤ p ⁻¹ᵁ chart 𝒜 f j) :
    (((cocycle 𝒜 f hf 1).inverseImage p).unit i j V hi hj : Γ(X, V)) =
      p.appLE (chart 𝒜 f i) V hi
        (Proj.awayToSection 𝒜 (f i) (coordinate 𝒜 f hf i j)) := by
  change p.appLE (chart 𝒜 f i ⊓ chart 𝒜 f j) V (le_inf hi hj)
    ((cocycle 𝒜 f hf 1).unit i j _ inf_le_left inf_le_right : Γ(Proj 𝒜, _)) = _
  rw [coefficient_unit_eq]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

end FLT.Mazur.GradedProjLine
