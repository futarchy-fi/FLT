/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteSupportClosedDescent
public import FLT.Mazur.CurveEulerCharacteristic
public import FLT.Mazur.ProperCoherentCohomology
public import FLT.Mazur.ModuleLineTensorExact

/-!
# Euler characteristic and finite-support comparisons

The Euler characteristic of coherent finite-support coefficients is unchanged
by tensoring with a line. Thus the change in Euler characteristic under a line
twist agrees for two coherent sheaves joined by a finite-support comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

open CoherentDevissage ModuleSheafTensor ModuleSheafTensorCurrying FLT.Mazur.GlobalIdealPower

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- Finite-support Euler characteristic is invariant under any line twist. -/
theorem curveEulerCharacteristic_finiteSupport_tensor
    (M : X.Modules) [M.IsFinitePresentation] (hM : (support M).Finite)
    {L : X.Modules} (hL : LocallyFreeRankOne L) :
    curveEulerCharacteristic f (tensor M L) = curveEulerCharacteristic f M :=
  curveEulerCharacteristic_iso f (finiteSupportLineTwistIso f M hM hL)

/-- Euler characteristic is additive for a coherent sequence with finite-support quotient. -/
theorem curveEulerCharacteristic_add_finiteSupport
    (S : ShortComplex X.Modules) (hS : CoherentSequence S)
    (hs : (support S.X₃).Finite) :
    curveEulerCharacteristic f S.X₂ =
      curveEulerCharacteristic f S.X₁ + curveEulerCharacteristic f S.X₃ := by
  have := hS.finite₁
  have := hS.finite₂
  have := hS.finite₃
  have : Module.Finite k (ModuleScalarH f S.X₁ 0) :=
    proper_coherent_hasFiniteCohomology f S.X₁ 0
  have : Module.Finite k (ModuleScalarH f S.X₂ 0) :=
    proper_coherent_hasFiniteCohomology f S.X₂ 0
  have : Module.Finite k (ModuleScalarH f S.X₃ 0) :=
    proper_coherent_hasFiniteCohomology f S.X₃ 0
  have : Module.Finite k (ModuleScalarH f S.X₁ 1) :=
    proper_coherent_hasFiniteCohomology f S.X₁ 1
  have : Module.Finite k (ModuleScalarH f S.X₂ 1) :=
    proper_coherent_hasFiniteCohomology f S.X₂ 1
  have : Subsingleton (ModuleScalarH f S.X₃ 1) :=
    finiteSupport_cohomology_subsingleton f S.X₃ hs 1 (by decide)
  exact curveEulerCharacteristic_add_of_surjective f S hS.shortExact
    (fun y ↦ ⟨0, Subsingleton.elim _ _⟩)

/-- A finite-support comparison preserves the change in Euler characteristic under a line twist. -/
theorem curveEulerCharacteristic_tensor_difference
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation]
    (a : M ⟶ N) [Mono a] (ha : (support (cokernel a)).Finite)
    {L : X.Modules} (hL : LocallyFreeRankOne L) :
    curveEulerCharacteristic f (tensor N L) - curveEulerCharacteristic f N =
      curveEulerCharacteristic f (tensor M L) - curveEulerCharacteristic f M := by
  have := Chow.source_isNoetherian f
  have := hL.isFinitePresentation
  have := coherent_cokernel a
  let S := ShortComplex.cokernelSequence a
  have hS := coherent_cokernelSequence a
  have hT : CoherentSequence (S.map (tensoring L)) :=
    ⟨ModuleLineTensorExact.shortExact S hS.shortExact L hL,
      tensor_coherent M L, tensor_coherent N L, tensor_coherent (cokernel a) L⟩
  have ht : (support (tensor (cokernel a) L)).Finite := by
    rw [support_iso (finiteSupportLineTwistIso f (cokernel a) ha hL)]
    exact ha
  have h₁ := curveEulerCharacteristic_add_finiteSupport f S hS ha
  have h₂ := curveEulerCharacteristic_add_finiteSupport f (S.map (tensoring L)) hT ht
  change curveEulerCharacteristic f N =
    curveEulerCharacteristic f M + curveEulerCharacteristic f (cokernel a) at h₁
  change curveEulerCharacteristic f (tensor N L) =
    curveEulerCharacteristic f (tensor M L) +
      curveEulerCharacteristic f (tensor (cokernel a) L) at h₂
  rw [curveEulerCharacteristic_finiteSupport_tensor f (cokernel a) ha hL] at h₂
  omega

end FLT.Mazur.FCurve
