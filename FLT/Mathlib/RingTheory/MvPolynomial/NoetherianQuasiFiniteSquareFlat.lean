/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.NoetherianFibreQuotientFlat
public import FLT.Mathlib.RingTheory.MvPolynomial.FiniteFibreParameterRegularity
public import FLT.Mathlib.RingTheory.MvPolynomial.BaseChangePresentation
public import Mathlib.RingTheory.QuasiFinite.Basic

/-! # Noetherian quasi-finite square presentations are flat -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace MvPolynomial

variable {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}

/-- A quasi-finite square polynomial presentation over a Noetherian base is flat.
Its specified equations become regular in the residue fibres by the finite-kernel criterion. -/
theorem flat_square_quotient_of_quasiFinite (rs : List (MvPolynomial (Fin n) R))
    (hlen : rs.length = n)
    [Algebra.QuasiFinite R (MvPolynomial (Fin n) R ⧸ Ideal.ofList rs)] :
    Module.Flat R (MvPolynomial (Fin n) R ⧸ Ideal.ofList rs) := by
  apply flat_quotient_of_residue_regular rs
  intro p _ Q _ hQ
  let f := Ideal.Quotient.mkₐ R (Ideal.ofList rs)
  let g := baseChangePresentation p.ResidueField f
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hg : Function.Surjective g := baseChangePresentation_surjective _ f hf
  have hker : RingHom.ker g = Ideal.ofList (rs.map (map (algebraMap R p.ResidueField))) := by
    change RingHom.ker (baseChangePresentation p.ResidueField f) = _
    rw [ker_baseChangePresentation _ f hf]
    have hk : RingHom.ker f = Ideal.ofList rs := Ideal.mk_ker
    rw [hk, Ideal.map_ofList]
  have hgen : Ideal.ofList ((rs.map (map (algebraMap R p.ResidueField))).map
      (algebraMap _ (Localization.AtPrime Q))) =
      (RingHom.ker g).map (algebraMap _ (Localization.AtPrime Q)) := by
    rw [hker, Ideal.map_ofList]
  exact (isRegular_finite_kernel_atPrime g hg Q (by rwa [hker]) _
    (by simpa using hlen) hgen).toIsWeaklyRegular

/-- The finite-tuple form retains the exact relation quotient used by coefficient descent. -/
theorem flat_square_range_quotient_of_quasiFinite (f : Fin n → MvPolynomial (Fin n) R)
    [Algebra.QuasiFinite R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))] :
    Module.Flat R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)) := by
  have hI : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_ofFn
  have : Algebra.QuasiFinite R (MvPolynomial (Fin n) R ⧸ Ideal.ofList (List.ofFn f)) :=
    (Algebra.QuasiFinite.iff_of_algEquiv (Ideal.quotientEquivAlgOfEq R hI)).mpr inferInstance
  have := flat_square_quotient_of_quasiFinite (List.ofFn f) (List.length_ofFn)
  exact Module.Flat.of_linearEquiv (Ideal.quotientEquivAlgOfEq R hI).symm.toLinearEquiv

end MvPolynomial
