/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeUnramified
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Etaleness constructed from free finite actions

The existing trace retraction makes the source finite projective over its
fixed ring. This supplies finite presentation and flatness. The constructed
separability tensor supplies the remaining unramifiedness, yielding etaleness
without Noetherian or characteristic restrictions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Finite G]
  (A : Type*) [CommRing A] [MulSemiringAction G A]
  (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

/-- Trace dual generators construct a finite presentation over the actual fixed ring. -/
theorem invariant_finitePresentation : Algebra.FinitePresentation (invariantRing G A) A := by
  let _ := invariant_module_finite G hfree
  let _ := invariant_module_projective G hfree
  let _ := Module.finitePresentation_of_projective (invariantRing G A) A
  infer_instance

/-- The full fixed-ring quotient is etale even in characteristics dividing the group order. -/
theorem invariant_etale : Algebra.Etale (invariantRing G A) A := by
  let _ := invariant_finitePresentation G A hfree
  let _ := invariant_module_projective G hfree
  let _ := invariant_formallyUnramified G A hfree
  exact Algebra.Etale.of_formallyUnramified_of_flat

end FLT.Mazur.FiniteGroupQuotient
