/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeGenericFreeness
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Entire quasi-finite algebras become finite free on a dense principal open

Generic freeness initially allows an infinite basis. A single residue-field
fiber of a quasi-finite algebra forces that basis to be finite. Applied to
the whole scalar extension, this retains every branch of the original algebra.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.QuasiFiniteGenericFiniteFree
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A free quasi-finite algebra over a nonzero ring has a finite basis. -/
theorem finite_of_free [Nontrivial R] [Module.Free R A] [Algebra.QuasiFinite R A] :
    Module.Finite R A := by
  let p : PrimeSpectrum R := Classical.choice inferInstance
  let b := Module.Free.chooseBasis R A
  let _ : Finite (Module.Free.ChooseBasisIndex R A) :=
    Module.Finite.finite_basis (b.baseChange p.asIdeal.ResidueField)
  exact Module.Finite.of_basis b

/-- One nonzero denominator makes the entire quasi-finite algebra finite free. -/
theorem exists_finite_free_baseChange [IsDomain R] [Algebra.FiniteType R A]
    [Algebra.QuasiFinite R A] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) ∧
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] A) := by
  obtain ⟨r, hr, hf⟩ := FiniteTypeGenericFreeness.exists_free_baseChange (R := R) (A := A)
  let _ := hf
  let _ := IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away r)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
  exact ⟨r, hr, hf, finite_of_free⟩

end FLT.Mazur.QuasiFiniteGenericFiniteFree
