/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.ResiduePresentationPoint
public import FLT.Mathlib.RingTheory.Flat.ResidueRegularLifting
public import FLT.Mathlib.RingTheory.MvPolynomial.TensorLocalRelations

/-! # Relative local equations from the actual residue-fibre presentation -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FinitePresentation R A] [Module.Flat R A] {d : ℕ}

/-- A regular square presentation of the actual residue fibre gives a square
presentation at the original target point, regular modulo its base prime.
The fibre point, finite kernel, radical ideal and comparison maps are constructed. -/
theorem exists_relative_local_regular_relations
    (f : MvPolynomial (Fin d) R →ₐ[R] A) (hf : Function.Surjective f)
    (Q : Ideal A) [Q.IsPrime]
    (h : ∀ (P : Ideal (MvPolynomial (Fin d) (Q.comap (algebraMap R A)).ResidueField))
      [P.IsPrime],
      RingHom.ker (baseChangePresentation (Q.comap (algebraMap R A)).ResidueField f) ≤ P →
      ∃ rs : List (Localization.AtPrime P), rs.length = d ∧
        Ideal.ofList rs =
          (RingHom.ker (baseChangePresentation (Q.comap (algebraMap R A)).ResidueField f)).map
            (algebraMap _ _) ∧
        RingTheory.Sequence.IsRegular (Localization.AtPrime P) rs) :
    ∃ ws : List (Localization.AtPrime (Q.comap (f : MvPolynomial (Fin d) R →+* A))),
      ws.length = d ∧
      Ideal.ofList ws = (RingHom.ker f).map (algebraMap (MvPolynomial (Fin d) R) _) ∧
      RingTheory.Sequence.IsRegular
        (Localization.AtPrime (Q.comap (f : MvPolynomial (Fin d) R →+* A)) ⧸
          (Q.comap (algebraMap R A)).map
            (algebraMap R (Localization.AtPrime (Q.comap (f : MvPolynomial (Fin d) R →+* A)))))
        (ws.map (Ideal.Quotient.mk ((Q.comap (algebraMap R A)).map (algebraMap R
          (Localization.AtPrime (Q.comap (f : MvPolynomial (Fin d) R →+* A))))))) := by
  let p := Q.comap (algebraMap R A)
  obtain ⟨q, hq, heq, hker⟩ := f.exists_residue_presentation_prime Q
  obtain ⟨rs, hlen, hgen, hreg⟩ := exists_tensor_local_regular_relations p.ResidueField f h q hker
  obtain ⟨ws, hlen', hgen', hreg'⟩ :=
    f.exists_local_kernel_list_of_residue_regular hf Q p le_rfl q heq rs hgen hreg
  exact ⟨ws, hlen'.trans hlen, hgen', hreg'⟩

end MvPolynomial
