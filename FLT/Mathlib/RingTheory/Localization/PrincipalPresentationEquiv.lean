/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Localization.QuotientAwayPresentation

/-! # Identify a principal presentation with the actual target chart -/

@[expose] public noncomputable section

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A]

/-- Generators of the full localized kernel present the actual target chart,
with its original coordinate map. No regularity or Noetherian hypothesis is needed. -/
theorem exists_principal_presentation_equiv (f : S →ₐ[R] A) (hf : Function.Surjective f)
    (a : S) (rs : List S)
    (hgen : Ideal.ofList (rs.map (algebraMap S (Localization.Away a))) =
      (RingHom.ker f).map (algebraMap S (Localization.Away a))) :
    ∃ e : (Localization.Away a ⧸
        Ideal.ofList (rs.map (algebraMap S (Localization.Away a)))) ≃ₐ[R]
        Localization.Away (f a),
      ∀ s : S, e (Ideal.Quotient.mk _ (algebraMap S _ s)) = algebraMap A _ (f s) := by
  let I := RingHom.ker f
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have he : (Submonoid.powers (Ideal.Quotient.mk I a)).map e.toMonoidHom =
      Submonoid.powers (f a) := by rw [Submonoid.map_powers]; rfl
  let e' := IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (Ideal.Quotient.mk I a)) (Localization.Away (f a)) e he
  let eqv := ((I.regularPresentationAwayEquiv a rs hgen).restrictScalars R).trans e'
  refine ⟨eqv, fun s ↦ ?_⟩
  change e' (I.regularPresentationAwayEquiv a rs hgen (algebraMap S _ s)) = _
  rw [Ideal.regularPresentationAwayEquiv_algebraMap,
    IsScalarTower.algebraMap_apply S (S ⧸ I)]
  exact IsLocalization.algEquivOfAlgEquiv_eq he _

end AlgHom
