/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAlgebraFiberSurjective
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Finite maps whose fibers are residue spectra

If every whole scheme fiber of a finite map is its target residue spectrum,
the map is a closed immersion. The proof detects affine ring surjectivity
by finite-module Nakayama, without assuming a reduced target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false
universe u

/-- Isomorphic residue fibers force a finite morphism to be a closed immersion. -/
theorem finite_isClosedImmersion_of_isIso_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (hf : ∀ y, IsIso (f.fiberToSpecResidueField y)) :
    IsClosedImmersion f := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ (fun y ↦ ?_) ⟨_, rfl⟩
    let _ := hf ((Y.affineCover.f i) y)
    exact (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f (Y.affineCover.f i)) y).isIso_snd_of_isIso
  obtain ⟨R, rfl⟩ := hY
  let _ : IsAffine X := isAffine_of_isAffineHom f
  wlog hX : ∃ B, X = Spec B generalizing X
  · have _ (y) : IsIso (pullback.snd f ((Spec R).fromSpecResidueField y)) := hf y
    have h : IsClosedImmersion (X.isoSpec.inv ≫ f) := by
      apply this _ (fun y ↦ ?_) ⟨_, rfl⟩
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      X.isoSpec.inv f).mp h
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  let _ : Module.Finite R B :=
    (IsFinite.SpecMap_iff φ).mp inferInstance
  apply IsClosedImmersion.spec_of_surjective
  apply finiteAlgebra_surjective_of_residue_fibers
  intro p
  have h := (Arrow.isIso_iff_isIso_of_isIso
    (Spec.fiberToSpecResidueFieldIso R B p).hom).mp (hf p)
  exact (isIso_SpecMap_iff.mp h).2

end FLT.Mazur.FCurve
