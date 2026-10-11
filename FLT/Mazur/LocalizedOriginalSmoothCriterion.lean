/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Formal smoothness from localized original cotangent obstructions

Localization commutes with original differentials and original H1. For an
essentially finite type Noetherian target, flatness of the former and
vanishing of the latter give formal smoothness of the localized algebra.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.LocalizedOriginalSmoothCriterion

open scoped TensorProduct

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [IsNoetherianRing B] [Algebra.EssFiniteType R B]
  (T : Submonoid A) [IsLocalization T B]

include T in
/-- The actual localized original cotangent obstructions imply formal smoothness. -/
theorem formallySmooth [Module.Flat B (B ⊗[A] Ω[A⁄R])]
    [Subsingleton (B ⊗[A] Algebra.H1Cotangent R A)] : Algebra.FormallySmooth R B := by
  let _ := Algebra.FormallyEtale.of_isLocalization (Rₘ := B) T
  let _ := Module.Flat.of_linearEquiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm
  let _ : Module.FinitePresentation B Ω[B⁄R] := Module.finitePresentation_of_finite B Ω[B⁄R]
  exact ⟨Module.Flat.projective_of_finitePresentation,
    (Algebra.tensorH1CotangentOfIsLocalization R B T).symm.subsingleton⟩

end FLT.Mazur.LocalizedOriginalSmoothCriterion
