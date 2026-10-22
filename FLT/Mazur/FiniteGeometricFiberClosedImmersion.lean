/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFiberClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Finite maps with trivial geometric scheme fibers

A geometric fiber isomorphism descends along the algebraic closure of the
actual target residue field. Finite-module Nakayama then makes the original
map a closed immersion, retaining nonreduced structure on the target.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

/-- Algebraically closed field tests suffice to detect a finite closed immersion. -/
theorem finite_isClosedImmersion_of_isIso_geometricFibers {X Y : Scheme}
    (f : X ⟶ Y) [IsFinite f]
    (hf : ∀ {K : Type} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Y),
      IsIso (pullback.snd f a)) : IsClosedImmersion f := by
  apply finite_isClosedImmersion_of_isIso_fibers f
  intro y
  let K := Y.residueField y
  let b := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  let a := Y.fromSpecResidueField y
  let _ : Flat b := inferInstance
  let _ : Surjective b := ⟨Function.surjective_to_subsingleton b⟩
  let _ : QuasiCompact b := inferInstance
  let _ := hf (b ≫ a)
  have h : IsIso (pullback.snd (pullback.snd f a) b) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f a b]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

end FLT.Mazur.FCurve
