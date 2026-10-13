/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericFreePolynomialQuotient
public import FLT.Mazur.PolynomialQuotientScalarExtension
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.FiniteType

/-!
# Generic freeness for finite type algebras over domains

Choose a finite polynomial presentation of the actual algebra and invert the
constructed leading-coefficient denominator of its kernel. Its scalar extension
is free, hence flat. Neither flatness nor finite generation of the kernel is
assumed; the basis can be infinite.
-/

@[expose] public noncomputable section
open MvPolynomial TensorProduct
namespace FLT.Mazur.FiniteTypeGenericFreeness
variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- A finite type algebra has an actual nonzero coefficient localization on which it is free. -/
theorem exists_free_baseChange [Algebra.FiniteType R A] :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  let I := RingHom.ker φ
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  let r := FiniteLeadingIdealFamily.denominator m I
  let S := Localization.Away r
  let e : S ⊗[R] (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[S] S ⊗[R] A :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (Ideal.quotientKerAlgEquivOfSurjective hφ)
  let _ := GenericFreePolynomialQuotient.quotient_free m I S
  refine ⟨r, FiniteLeadingIdealFamily.denominator_ne_zero m I, ?_⟩
  exact Module.Free.of_equiv
    (((PolynomialQuotientScalarExtension.equiv S I).symm.trans e).toLinearEquiv)

/-- Generic flatness is a consequence of the constructed free scalar extension. -/
theorem exists_flat_baseChange [Algebra.FiniteType R A] :
    ∃ r : R, r ≠ 0 ∧ Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] A) := by
  obtain ⟨r, hr, hf⟩ := exists_free_baseChange (R := R) (A := A)
  let _ := hf
  exact ⟨r, hr, Module.Flat.of_free⟩

end FLT.Mazur.FiniteTypeGenericFreeness
