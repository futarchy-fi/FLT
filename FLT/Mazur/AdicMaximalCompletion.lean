/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Maximal ideals of completions of nonlocal rings

Completing a ring at a finitely generated maximal ideal gives a local ring,
whose maximal ideal is the extension of the original one. Formal algebra
equivalences consequently preserve these extended ideals.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicMaximalCompletion

variable {A : Type*} [CommRing A] (I : Ideal A) [I.IsMaximal] (hI : I.FG)

include hI

/-- Completion at a finite maximal ideal is local, even when the original ring is not. -/
theorem localRing : IsLocalRing (AdicCompletion I A) := by
  let _ := AdicCompletion.isMaximal_map_of_le I I le_rfl hI
  let _ := AdicCompletion.isAdicComplete_self I hI
  exact isLocalRing_of_isAdicComplete_maximal
    (I.map (algebraMap A (AdicCompletion I A)))

/-- The extended ideal is exactly the maximal ideal of the completed ring. -/
theorem maximalIdeal_eq [IsLocalRing (AdicCompletion I A)] :
    IsLocalRing.maximalIdeal (AdicCompletion I A) =
      I.map (algebraMap A (AdicCompletion I A)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I I le_rfl hI)).symm

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R A] [Algebra R B]
  (J : Ideal B) [J.IsMaximal] (hJ : J.FG)

include hJ

/-- Formal algebra equivalences preserve the extended maximal ideals. -/
theorem map_ideal_le (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B) :
    (I.map (algebraMap A (AdicCompletion I A))).map e.toAlgHom.toRingHom ≤
      J.map (algebraMap B (AdicCompletion J B)) := by
  let _ := localRing I hI
  let _ := localRing J hJ
  let _ : IsLocalHom e.toAlgHom.toRingHom := IsLocalHom.of_surjective _ e.surjective
  rw [← maximalIdeal_eq I hI, ← maximalIdeal_eq J hJ]
  exact IsLocalRing.map_maximalIdeal_le e.toAlgHom.toRingHom

end FLT.Mazur.AdicMaximalCompletion
