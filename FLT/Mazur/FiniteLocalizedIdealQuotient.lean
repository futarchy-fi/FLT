/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePresentedFlatQuotientIdeal
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Presenting ideals on finite branches of a quotient

A principal localization of the ambient has the same full quotient as the
corresponding localization of the original quotient. A finite presented flat
branch therefore constructs a presentation of the localized ambient ideal.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- The full ideal quotient commutes with principal ambient localization. -/
def localizedIdealQuotientEquiv (I : Ideal B) (s : B) :
    Localization.Away (Ideal.Quotient.mk I s) ≃ₐ[R]
      (Localization.Away s ⧸ I.map (algebraMap B (Localization.Away s))) := by
  let D := Localization.Away s
  let J := I.map (algebraMap B D)
  let _ : IsScalarTower R (B ⧸ I) (D ⧸ J) := .to₁₃₄ R B _ _
  let _ : IsLocalization.Away (Ideal.Quotient.mk I s) (D ⧸ J) := by
    convert (inferInstance :
      IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ I) (.powers s)) (D ⧸ J)) using 1
    simp [Algebra.algebraMapSubmonoid]
  exact (IsLocalization.algEquiv (.powers (Ideal.Quotient.mk I s))
    (Localization.Away (Ideal.Quotient.mk I s)) (D ⧸ J)).restrictScalars R

/-- Finiteness of a quotient branch is finiteness of the actual localized ideal quotient. -/
theorem finite_localized_ideal_quotient (I : Ideal B) (s : B)
    [Module.Finite R (Localization.Away (Ideal.Quotient.mk I s))] :
    Module.Finite R (Localization.Away s ⧸
      I.map (algebraMap B (Localization.Away s))) :=
  Module.Finite.equiv (localizedIdealQuotientEquiv (R := R) I s).toLinearEquiv

/-- A finite flat branch of a presented quotient supplies the ambient ideal presentation. -/
theorem finitePresentation_ideal_on_finite_branch [Algebra.FinitePresentation R B]
    (I : Ideal B) [Algebra.FinitePresentation R (B ⧸ I)] [Module.Flat R (B ⧸ I)] (s : B)
    [Module.Finite R (Localization.Away (Ideal.Quotient.mk I s))] :
    Module.FinitePresentation (Localization.Away s)
      (I.map (algebraMap B (Localization.Away s))) := by
  let D := Localization.Away s
  let J := I.map (algebraMap B D)
  let _ : IsScalarTower R (B ⧸ I) (D ⧸ J) := .to₁₃₄ R B _ _
  let e := localizedIdealQuotientEquiv (R := R) I s
  let _ : Module.Finite R (D ⧸ J) := finite_localized_ideal_quotient I s
  let _ : Algebra.FinitePresentation R (D ⧸ J) :=
    Algebra.FinitePresentation.equiv e
  let _ : Module.FinitePresentation R (D ⧸ J) :=
    Module.FinitePresentation.of_finite_of_finitePresentation R (D ⧸ J)
  let _ : Module.Flat R (D ⧸ J) := Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  exact ideal_finitePresentation_of_finitePresentation_flat_quotient (R := R) J

end FLT.Mazur.FCurve
