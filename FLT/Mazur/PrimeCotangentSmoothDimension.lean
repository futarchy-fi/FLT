/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedCotangentFieldRank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Relative dimension near a smooth prime from its actual cotangent fiber

A rank computation at a single prime produces a standard-smooth principal
neighborhood of that relative dimension in the original affine scheme.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrimeCotangentSmoothDimension

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FinitePresentation R A] (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt R p]

/-- A smooth prime has a standard-smooth principal neighborhood of its cotangent rank. -/
theorem exists_notMem_relativeDimension (d : ℕ)
    (hr : Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) = d) :
    ∃ f : A, f ∉ p ∧
      Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away f) := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  let L := Localization.Away f
  let _ := hstd
  have hu : IsUnit (algebraMap A p.ResidueField f) :=
    isUnit_iff_ne_zero.mpr (mt Ideal.algebraMap_residueField_eq_zero.mp hf)
  let g : L →+* p.ResidueField := IsLocalization.Away.lift f hu
  let _ := g.toAlgebra
  let _ : IsScalarTower A L p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (IsLocalization.Away.lift_eq (S := L) f hu a).symm)
  refine ⟨f, hf, ?_⟩
  apply (StandardSmoothFieldCotangentRank.relativeDimension_iff R L p.ResidueField d).mpr
  rw [← LocalizedCotangentFieldRank.finrank_eq R A L p.ResidueField]
  exact hr

end FLT.Mazur.PrimeCotangentSmoothDimension
