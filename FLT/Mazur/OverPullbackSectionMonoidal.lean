/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackSection

/-!
# Monoidal base change of actual sections

The monoidal unit comparison followed by the pulled-back section is exactly
the section determined by its original projection. This connects abstract
monoidal base change with explicit relative points without unfolding group laws.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OverPullbackSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T : Scheme.{u}} (f : T ⟶ S) (G : Over S)

/-- The monoidal unit comparison retains the original base morphism. -/
theorem unit_fst : (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
    pullback.fst (𝟙 S) f = f := by
  rw [Over.ε_pullback_left]
  have h : pullback.fst (𝟙 S) f = pullback.snd (𝟙 S) f ≫ f := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 S) (g := f))
  rw [h, IsIso.inv_hom_id_assoc]

/-- Monoidal pullback of a section projects to the original section after the base map. -/
@[reassoc] theorem monoidal_section_fst (s : 𝟙_ (Over S) ⟶ G) :
    (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s).left ≫
      pullback.fst G.hom f = f ≫ s.left := by
  change (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
    pullback.lift (pullback.fst (𝟙 S) f ≫ s.left) (pullback.snd (𝟙 S) f) _ ≫
      pullback.fst G.hom f = f ≫ s.left
  rw [pullback.lift_fst, ← Category.assoc, unit_fst]

/-- The abstract monoidal section is the explicit lift of its original relative point. -/
theorem monoidal_section_eq_lift (s : 𝟙_ (Over S) ⟶ G)
    (p : Over.mk f ⟶ G) (hp : p.left = f ≫ s.left) :
    Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map s = lift f G p := by
  apply hom_ext
  rw [monoidal_section_fst, lift_fst, hp]

end FLT.Mazur.OverPullbackSection
