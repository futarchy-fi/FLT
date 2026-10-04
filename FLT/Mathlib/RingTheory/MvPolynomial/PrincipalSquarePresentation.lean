/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.MvPolynomial.RelationQuotientPresentation
public import FLT.Mathlib.RingTheory.Localization.PrincipalPresentationEquiv

/-! # Encode a square principal chart as a square polynomial presentation -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}

/-- Add one variable and its inverse equation to a square principal presentation.
The result presents the actual original chart, not an unspecified isomorphic algebra. -/
theorem exists_principal_square_presentation
    (f : MvPolynomial (Fin d) R →ₐ[R] A) (hf : Function.Surjective f)
    (a : MvPolynomial (Fin d) R) (rs : List (MvPolynomial (Fin d) R))
    (hlen : rs.length = d)
    (hgen : Ideal.ofList (rs.map (algebraMap _ (Localization.Away a))) =
      (RingHom.ker f).map (algebraMap _ (Localization.Away a))) :
    Nonempty (Algebra.Presentation R (Localization.Away (f a)) (Fin (d + 1)) (Fin (d + 1))) := by
  classical
  have hI : Ideal.span (Set.range rs.get) = Ideal.ofList rs := by
    apply congrArg Ideal.span
    ext x
    exact List.mem_iff_get.symm
  let P := (relationQuotientPresentation rs.get).ofAlgEquiv (Ideal.quotientEquivAlgOfEq R hI)
  let Q := (Algebra.Presentation.localizationAway
    (Localization.Away (Ideal.Quotient.mk (Ideal.ofList rs) a))
    (Ideal.Quotient.mk (Ideal.ofList rs) a)).comp P
  let ev : Fin (d + 1) ≃ Unit ⊕ Fin d := (Fintype.equivFinOfCardEq (by simp [Nat.add_comm])).symm
  let er : Fin (d + 1) ≃ Unit ⊕ Fin rs.length :=
    (Fintype.equivFinOfCardEq (by simp [hlen, Nat.add_comm])).symm
  obtain ⟨e, _⟩ := f.exists_principal_presentation_equiv hf a rs hgen
  let e₀ := ((Ideal.ofList rs).regularPresentationAwayEquiv a rs
    (by rw [Ideal.map_ofList])).restrictScalars R
  exact ⟨((Q.reindex ev er).ofAlgEquiv (e₀.symm.trans e))⟩

end MvPolynomial
