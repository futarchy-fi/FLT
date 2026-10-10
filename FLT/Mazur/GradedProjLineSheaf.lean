/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjLineSectionCocycle
public import FLT.Mazur.ModuleSheafUnitCocycleRestrict
public import FLT.Mazur.PrincipalSectionExtension

/-!
# Line sheaves from homogeneous coordinates on Proj

The homogeneous ratios construct an actual sheaf. A covering coordinate
family makes it locally free of rank one and finitely presented.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.GradedProjLine

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The homogeneous transition units on every common subopen. -/
def cocycle (n : ℤ) : Cocycle (chart 𝒜 f) :=
  Cocycle.ofOverlap (twistTransition 𝒜 f hf n) (twistTransition_self 𝒜 f hf n) (by
    intro i j k V hi hj hk
    have h := congrArg (restrictUnits 𝒜 (le_inf (le_inf hi hj) hk))
      (twistTransition_cocycle 𝒜 f hf n i j k)
    simp only [map_mul, restrictUnits_comp] at h
    exact congrArg Units.val h)

/-- The sheaf glued using powers of the actual homogeneous ratios. -/
def line (n : ℤ) : (Proj 𝒜).Modules := (cocycle 𝒜 f hf n).sheaf

/-- Its specified chart trivialization is coefficient evaluation. -/
def lineRestrictIso (n : ℤ) (i : ι) :
    (line 𝒜 f hf n).restrict (chart 𝒜 f i).ι ≅
      structureModule (chart 𝒜 f i).toScheme := (cocycle 𝒜 f hf n).restrictIso i

/-- A cover by the given homogeneous coordinates proves the line property. -/
theorem line_rankOne (n : ℤ) (hcover : (⨆ i, Proj.basicOpen 𝒜 (f i)) = ⊤) :
    LocallyFreeRankOne (line 𝒜 f hf n) :=
  (cocycle 𝒜 f hf n).locallyFreeRankOne hcover

/-- The constructed line sheaf is coherent in the finite-presentation sense. -/
theorem line_isFinitePresentation (n : ℤ)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (f i)) = ⊤) :
    (line 𝒜 f hf n).IsFinitePresentation :=
  (line_rankOne 𝒜 f hf n hcover).isFinitePresentation

/-- Local coefficient changes retain the original homogeneous transition units. -/
theorem line_change (n : ℤ) (i j : ι) (V : (Proj 𝒜).Opens)
    (hi : V ≤ chart 𝒜 f i) (hj : V ≤ chart 𝒜 f j)
    (W : V.toScheme.Opens) (r : Γ(V.toScheme, W)) :
    (((cocycle 𝒜 f hf n).onOpenIso j V hj).inv ≫
      ((cocycle 𝒜 f hf n).onOpenIso i V hi).hom).app W r =
      ((cocycle 𝒜 f hf n).unit i j (V.ι ''ᵁ W)
        ((V.ι_image_le W).trans hi) ((V.ι_image_le W).trans hj) :
          Γ(Proj 𝒜, V.ι ''ᵁ W)) * (show Γ(Proj 𝒜, V.ι ''ᵁ W) from r) :=
  (cocycle 𝒜 f hf n).onOpenIso_change i j V hi hj W r

end FLT.Mazur.GradedProjLine
