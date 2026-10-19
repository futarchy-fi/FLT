/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CartesianFiniteFibers

/-!
# Base change of an actual section cover

The original sections pull back to sections covering the entire new source.
The result retains the original projection and does not discard residue branches.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SectionCoverBaseChange
universe u v
variable {X Y T : Scheme.{u}} (p : X ⟶ Y) (g : T ⟶ Y)
  (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)

/-- Pull back the original section along the specified base morphism. -/
def sectionMap : T ⟶ pullback p g :=
  pullback.lift (g ≫ s) (𝟙 T) (by rw [Category.assoc, hs]; simp)

/-- The pulled-back point retains its exact original source map. -/
@[reassoc] theorem sectionMap_fst :
    sectionMap p g s hs ≫ pullback.fst p g = g ≫ s :=
  pullback.lift_fst _ _ _

/-- The pulled-back morphism is an actual section. -/
@[reassoc] theorem sectionMap_snd :
    sectionMap p g s hs ≫ pullback.snd p g = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- The section square itself is Cartesian. -/
theorem sectionMap_isPullback :
    IsPullback (sectionMap p g s hs) g (pullback.fst p g) s := by
  apply IsPullback.of_right (h₁₂ := pullback.snd p g) (h₂₂ := p)
    (v₁₃ := g) _ (sectionMap_fst p g s hs) (IsPullback.of_hasPullback p g).flip
  rw [sectionMap_snd, hs]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Its image is precisely the inverse image of the original section image. -/
theorem sectionMap_range :
    Set.range (sectionMap p g s hs) = (pullback.fst p g) ⁻¹' Set.range s :=
  CartesianFiniteFibers.range_eq_preimage (sectionMap_isPullback p g s hs).flip

/-- A cover by actual sections remains a cover after arbitrary base change. -/
theorem covers {I : Type v} (r : I → (Y ⟶ X))
    (hr : ∀ i, r i ≫ p = 𝟙 Y) (hc : ∀ x : X, ∃ i, r i (p x) = x) :
    ∀ x : (pullback p g : Scheme.{u}),
      ∃ i, sectionMap p g (r i) (hr i) (pullback.snd p g x) = x := by
  intro x
  obtain ⟨i, hi⟩ := hc (pullback.fst p g x)
  have hx : x ∈ Set.range (sectionMap p g (r i) (hr i)) := by
    rw [sectionMap_range]
    exact ⟨_, hi⟩
  obtain ⟨z, rfl⟩ := hx
  refine ⟨i, ?_⟩
  have hz := congrArg (fun m : T ⟶ T ↦ m z) (sectionMap_snd p g (r i) (hr i))
  change sectionMap p g (r i) (hr i) ((sectionMap p g (r i) (hr i) ≫
    pullback.snd p g) z) = _
  rw [hz]
  rfl

end FLT.Mazur.SectionCoverBaseChange
