/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryIndependentFlatTests
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# Scalar test descent along actual fppf covers of the scalar base

An arbitrary small fppf cover supplies an actual point over the original prime.
Independent test equations there can use functions of the covering scalar
scheme. Descent constructs one original denominator without a finite cover
hypothesis, and without requiring any branch function to be an original scalar.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
  (C : Scheme.Cover.{0} Scheme.fppfPrecoverage (Spec (.of T))) (P : PrimeSpectrum T)
local notation "π" => boundaryScalarProjection s κ

/-- The actual cover supplies the branch point; the functions are chosen independently per test. -/
theorem boundaryScalar_mem_of_fppf_scalar_tests
    (h : ∀ i, ∀ y : C.X i, C.f i y = P → ∀ t ∈ a,
      ∃ (x : Γ(C.X i, ⊤)) (order : ℕ), y ∈ (C.X i).basicOpen x ∧
        ((pullback.fst π (C.f i)).appTop (boundaryCoordinate s κ t)) ^ order *
          (pullback.snd π (C.f i)).appTop x = 0) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  let D : (Spec (.of T)).Cover
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
  obtain ⟨i, y, hy⟩ := D.exists_eq P
  let _ : Flat (C.f i) := (D.map_prop i).1
  let _ : LocallyOfFinitePresentation (C.f i) := (D.map_prop i).2
  choose x k hx he using fun t : a ↦ h i y hy t.val t.property
  exact boundaryScalar_mem_of_independent_flat_tests s κ a
    (fun _ ↦ C.X i) (fun _ ↦ C.f i) P (fun _ ↦ y) (fun _ ↦ hy) x hx
    (fun t ↦ ⟨k t, he t⟩)

/-- Fppf scalar tests construct a denominator in the full original scalar ring. -/
theorem boundaryScalar_denominator_of_fppf_scalar_tests
    (h : ∀ i, ∀ y : C.X i, C.f i y = P → ∀ t ∈ a,
      ∃ (x : Γ(C.X i, ⊤)) (order : ℕ), y ∈ (C.X i).basicOpen x ∧
        ((pullback.fst π (C.f i)).appTop (boundaryCoordinate s κ t)) ^ order *
          (pullback.snd π (C.f i)).appTop x = 0) :
    ∃ (order : ℕ) (r : T), r ∉ P.asIdeal ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator :=
  (mem_boundaryScalarNilpotenceOpen s κ a P).mp
    (boundaryScalar_mem_of_fppf_scalar_tests s κ a C P h)

end FLT.Mazur.AffineScalarBoundaryNilpotence
