/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Detecting properness with an immersed proper cover

A proper surjective cover immersed in a proper scheme detects properness of
its target: after any base change, the target is proper exactly when the
immersion becomes closed. No flatness assumption on the base change is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Approximation

variable {Z P X S T : Scheme.{u}}

/-- Base change of a morphism with a specified identity over the base. -/
def immersionBaseChange (q : Z ⟶ S) (p : P ⟶ S) (h : Z ⟶ P)
    (w : h ≫ p = q) (b : T ⟶ S) : pullback q b ⟶ pullback p b :=
  pullback.lift (pullback.fst q b ≫ h) (pullback.snd q b)
    (by rw [Category.assoc, w, pullback.condition])

@[reassoc (attr := simp)]
lemma immersionBaseChange_fst (q : Z ⟶ S) (p : P ⟶ S) (h : Z ⟶ P)
    (w : h ≫ p = q) (b : T ⟶ S) :
    immersionBaseChange q p h w b ≫ pullback.fst p b = pullback.fst q b ≫ h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma immersionBaseChange_snd (q : Z ⟶ S) (p : P ⟶ S) (h : Z ⟶ P)
    (w : h ≫ p = q) (b : T ⟶ S) :
    immersionBaseChange q p h w b ≫ pullback.snd p b = pullback.snd q b :=
  pullback.lift_snd _ _ _

/-- The displayed map is cartesian over the original morphism. -/
lemma immersionBaseChange_isPullback (q : Z ⟶ S) (p : P ⟶ S) (h : Z ⟶ P)
    (w : h ≫ p = q) (b : T ⟶ S) :
    IsPullback (immersionBaseChange q p h w b) (pullback.fst q b)
      (pullback.fst p b) h := by
  apply IsPullback.of_right (h₁₂ := pullback.snd p b) (h₂₂ := p) (v₁₃ := b)
    ?_ (immersionBaseChange_fst q p h w b)
    (IsPullback.of_hasPullback p b).flip
  simpa only [immersionBaseChange_snd, w] using (IsPullback.of_hasPullback q b).flip

/-- A proper surjective cover with an immersion into a proper ambient scheme
reduces properness after arbitrary base change to closedness of that immersion. -/
theorem proper_baseChange_iff_closedImmersion
    (f : X ⟶ S) (p : P ⟶ S) (π : Z ⟶ X) (h : Z ⟶ P)
    [IsSeparated f] [LocallyOfFiniteType f] [IsProper p]
    [IsProper π] [Surjective π] [IsImmersion h]
    (w : h ≫ p = π ≫ f) (b : T ⟶ S) :
    IsProper (pullback.snd f b) ↔
      IsClosedImmersion (immersionBaseChange (π ≫ f) p h w b) := by
  let πb := immersionBaseChange (π ≫ f) f π rfl b
  let hb := immersionBaseChange (π ≫ f) p h w b
  have hπ := (immersionBaseChange_isPullback (π ≫ f) f π rfl b).flip
  have : IsProper πb := MorphismProperty.of_isPullback hπ inferInstance
  have : Surjective πb := MorphismProperty.of_isPullback hπ inferInstance
  have : IsImmersion hb := MorphismProperty.of_isPullback
    (immersionBaseChange_isPullback (π ≫ f) p h w b).flip inferInstance
  have he : hb ≫ pullback.snd p b = πb ≫ pullback.snd f b := by
    simp only [hb, πb, immersionBaseChange_snd]
  constructor
  · intro hf
    let := hf
    have : IsProper (hb ≫ pullback.snd p b) := by rw [he]; infer_instance
    have : IsProper hb := IsProper.of_comp hb (pullback.snd p b)
    exact IsClosedImmersion.of_isPreimmersion hb hb.isClosedMap.isClosed_range
  · intro hh
    have : IsClosedImmersion hb := hh
    have : UniversallyClosed (πb ≫ pullback.snd f b) := by rw [← he]; infer_instance
    have : UniversallyClosed (pullback.snd f b) :=
      UniversallyClosed.of_comp_surjective πb (pullback.snd f b)
    exact ⟨⟩

end FLT.Mazur.Approximation
