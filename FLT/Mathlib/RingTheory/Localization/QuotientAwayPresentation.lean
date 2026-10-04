/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Identify principal quotient charts with their localized presentations -/

@[expose] public noncomputable section

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) (a : R)

/-- Localizing a quotient at the image of `a` is the quotient of the localization. -/
theorem quotient_isLocalizationAway :
    IsLocalization.Away (Ideal.Quotient.mk I a)
      (Localization.Away a ⧸ I.map (algebraMap R (Localization.Away a))) := by
  change IsLocalization (Submonoid.powers (algebraMap R (R ⧸ I) a)) _
  rw [← Algebra.algebraMapSubmonoid_powers]
  infer_instance

/-- The actual principal chart of a quotient, with the original scalar structure. -/
def quotientAwayEquiv :
    (Localization.Away a ⧸ I.map (algebraMap R (Localization.Away a))) ≃ₐ[R ⧸ I]
      Localization.Away (Ideal.Quotient.mk I a) := by
  have := I.quotient_isLocalizationAway a
  exact IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I a)) _ _

/-- A relation list generating the localized kernel presents the actual principal chart. -/
def regularPresentationAwayEquiv (rs : List R)
    (h : Ideal.ofList (rs.map (algebraMap R (Localization.Away a))) =
      I.map (algebraMap R (Localization.Away a))) :
    (Localization.Away a ⧸ Ideal.ofList (rs.map (algebraMap R (Localization.Away a)))) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk I a) :=
  (Ideal.quotientEquivAlgOfEq R h).trans ((I.quotientAwayEquiv a).restrictScalars R)

/-- The chart identification keeps the original coordinates. -/
theorem regularPresentationAwayEquiv_algebraMap (rs : List R)
    (h : Ideal.ofList (rs.map (algebraMap R (Localization.Away a))) =
      I.map (algebraMap R (Localization.Away a))) (r : R) :
    I.regularPresentationAwayEquiv a rs h (algebraMap R _ r) = algebraMap R _ r :=
  (I.regularPresentationAwayEquiv a rs h).commutes r

end Ideal
