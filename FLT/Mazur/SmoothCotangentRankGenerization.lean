/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrimeCotangentSmoothDimension

/-!
# Cotangent ranks specialize constantly on a smooth neighborhood

A standard-smooth principal neighborhood computes every residue-field
cotangent rank on that neighborhood. In particular the rank at a smooth
specialization determines the rank of all its generizations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.SmoothCotangentRankGenerization

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- A standard-smooth principal chart computes the original cotangent fiber at every point in it. -/
theorem finrank_eq_of_away (f : A) (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away f)]
    (p : Ideal A) [p.IsPrime] (hf : f ∉ p) :
    Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) = d := by
  let L := Localization.Away f
  let _ : Algebra.IsStandardSmooth R L :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := d)
  have hu : IsUnit (algebraMap A p.ResidueField f) :=
    isUnit_iff_ne_zero.mpr (mt Ideal.algebraMap_residueField_eq_zero.mp hf)
  let g : L →+* p.ResidueField := IsLocalization.Away.lift f hu
  let _ := g.toAlgebra
  let _ : IsScalarTower A L p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (IsLocalization.Away.lift_eq (S := L) f hu a).symm)
  rw [LocalizedCotangentFieldRank.finrank_eq R A L p.ResidueField]
  exact (StandardSmoothFieldCotangentRank.relativeDimension_iff R L p.ResidueField d).mp
    inferInstance

/-- The cotangent rank at a smooth prime equals its rank at every generization. -/
theorem finrank_eq_of_le [Algebra.FinitePresentation R A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] [Algebra.IsSmoothAt R p] (hqp : q ≤ p) :
    Module.finrank q.ResidueField (q.ResidueField ⊗[A] Ω[A⁄R]) =
      Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R]) := by
  obtain ⟨f, hf, hstd⟩ := PrimeCotangentSmoothDimension.exists_notMem_relativeDimension
    R A p (Module.finrank p.ResidueField (p.ResidueField ⊗[A] Ω[A⁄R])) rfl
  let _ := hstd
  exact finrank_eq_of_away R A f _ q (fun hq ↦ hf (hqp hq))

end FLT.Mazur.SmoothCotangentRankGenerization
