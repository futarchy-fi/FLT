/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Faithfully flat descent of finite presentation for modules

First descend a finite generating family. The kernel of the resulting finite
free presentation commutes with flat tensoring, and its finite generation
descends too. This supplies the algebraic input to Cartier-neighborhood descent.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S]

/-- Finite presentation of modules descends under a faithfully flat coefficient extension. -/
theorem finitePresentation_of_faithfullyFlat
    [Module.FinitePresentation S (S ⊗[R] M)] : Module.FinitePresentation R M := by
  let : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  apply Module.finitePresentation_of_free_of_surjective f hf
  have hk : (LinearMap.ker (AlgebraTensorModule.lTensor S S f)).FG :=
    Module.FinitePresentation.fg_ker _ (LinearMap.lTensor_surjective S hf)
  let : Module.Finite S (LinearMap.ker (AlgebraTensorModule.lTensor S S f)) :=
    Module.Finite.of_fg hk
  let : Module.Finite S (S ⊗[R] LinearMap.ker f) :=
    Module.Finite.equiv (LinearMap.tensorKerEquiv S S f).symm
  let : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact Module.Finite.iff_fg.mp inferInstance

/-- Faithfully flat scalar extension detects finite presentation exactly. -/
theorem finitePresentation_faithfullyFlat_iff :
    Module.FinitePresentation S (S ⊗[R] M) ↔ Module.FinitePresentation R M :=
  ⟨fun _ ↦ finitePresentation_of_faithfullyFlat (S := S), fun _ ↦ inferInstance⟩

end FLT.Mazur.FCurve
