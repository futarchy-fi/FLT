/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfSchemeCover

/-!
# One fppf cover lifting both independent endpoints

Two maps into a covered scheme lift simultaneously after two actual pullbacks.
The construction imposes no equality on the endpoints or their translation bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.RelativeFppfPairCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {U V T : Over S} (g : U ⟶ V) (a b : T ⟶ V)

/-- First lift the first endpoint, then independently lift the second endpoint. -/
def source : Over S := pullback (pullback.fst a g ≫ b) g

/-- The composite actual cover of the original test scheme. -/
def cover : source g a b ⟶ T := pullback.fst _ _ ≫ pullback.fst a g

/-- The first lifted endpoint. -/
def fst : source g a b ⟶ U := pullback.fst _ _ ≫ pullback.snd a g

/-- The second lifted endpoint. -/
def snd : source g a b ⟶ U := pullback.snd _ _

/-- Both first endpoint morphisms agree over the original scheme. -/
@[reassoc]
theorem fst_map : fst g a b ≫ g = cover g a b ≫ a := by
  dsimp only [fst, cover]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

/-- The second endpoint has an independent lift over the same covering test. -/
@[reassoc]
theorem snd_map : snd g a b ≫ g = cover g a b ≫ b := by
  dsimp only [snd, cover]
  rw [Category.assoc]
  exact pullback.condition.symm

private theorem pullback_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {A B C : Over S} (f : A ⟶ C) (h : B ⟶ C)
    (hh : P h.left) : P (pullback.fst f h).left :=
  P.of_isPullback ((IsPullback.of_hasPullback f h).map (Over.forget _)).flip hh

/-- Any composition- and base-change-stable property of the cover holds for this pair cover. -/
theorem cover_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] (hg : P g.left) :
    P (cover g a b).left := by
  dsimp only [cover, Over.comp_left]
  exact P.comp_mem _ _ (pullback_property P _ _ hg) (pullback_property P _ _ hg)

instance cover_flat [Flat g.left] : Flat (cover g a b).left :=
  cover_property g a b (@Flat) inferInstance

instance cover_locallyOfFinitePresentation [LocallyOfFinitePresentation g.left] :
    LocallyOfFinitePresentation (cover g a b).left :=
  cover_property g a b (@LocallyOfFinitePresentation) inferInstance

instance cover_surjective [Surjective g.left] : Surjective (cover g a b).left :=
  cover_property g a b (@Surjective) inferInstance

instance cover_etale [Etale g.left] : Etale (cover g a b).left :=
  cover_property g a b (@Etale) inferInstance

/-- These are genuine simultaneous lifts along a single constructed fppf morphism. -/
theorem exists_fppf_lifts [Flat g.left] [LocallyOfFinitePresentation g.left]
    [Surjective g.left] :
    ∃ (W : Over S) (t : W ⟶ T) (a' b' : W ⟶ U),
      Flat t.left ∧ LocallyOfFinitePresentation t.left ∧ Surjective t.left ∧
        a' ≫ g = t ≫ a ∧ b' ≫ g = t ≫ b :=
  ⟨source g a b, cover g a b, fst g a b, snd g a b, inferInstance, inferInstance,
    inferInstance, fst_map g a b, snd_map g a b⟩

end FLT.Mazur.RelativeFppfPairCover
