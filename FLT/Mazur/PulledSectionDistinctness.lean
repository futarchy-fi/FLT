/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSectionBaseChange
public import FLT.Mazur.UniversallyDistinctSections

/-!
# Testing distinctness on actual pulled-back sections

Injectivity of the sections on every nonempty base change implies the
universal distinctness predicate on relative points. The pullback comparison
uses both projections, so the test applies to arbitrary base schemes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.UniversallyDistinctSections
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {X : Over S} {A : Type}
  (m : A → (𝟙_ (Over S) ⟶ X))

/-- Testing actual pulled-back sections suffices for universal distinctness. -/
theorem universallyDistinct_of_pull_injective
    (hm : ∀ (T : Scheme) (g : T ⟶ S), Nonempty T →
      Function.Injective (fun i ↦ pullSection g (m i))) : UniversallyDistinct m := by
  intro V k hV i j hij
  apply hm V.left V.hom hV
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [section_fst, section_fst]
    have hk : k.left = V.hom := by simpa using k.w
    have h := congrArg (fun s : V ⟶ X ↦ s.left) hij
    simpa only [Over.comp_left, hk] using h
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.UniversallyDistinctSections
