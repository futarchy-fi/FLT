/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeQuotientIdealPresentation
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite flat quotients over an arbitrary local base

Finite flat modules over a local ring are free. Applying the integer-chart
construction to this actual basis proves finite presentation of the ideal
inside a finitely presented ambient algebra, even for a non-Noetherian base.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
variable {R B : Type*} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
  [Algebra.FinitePresentation R B]

/-- A finite flat quotient over a local base has a finitely presented ambient ideal. -/
theorem ideal_finitePresentation_of_local_finite_flat (I : Ideal B)
    [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)] :
    Module.FinitePresentation B I := by
  let _ : Module.Free R (B ⧸ I) := Module.free_of_flat_of_isLocalRing
  exact ideal_finitePresentation_of_quotient_basis I (Module.finBasis R (B ⧸ I))

end FLT.Mazur.FCurve
