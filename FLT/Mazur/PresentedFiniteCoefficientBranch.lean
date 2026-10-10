/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocalizedIdealQuotient
public import FLT.Mazur.QuasiFiniteCoefficientQuotient

/-!
# Ideal presentations on actual finite coefficient branches

Start with a finitely presented ambient and flat finitely presented quotient
algebra. Any finite branch after coefficient change has a finitely presented
full ideal. The original quotient need not be module-finite, and its ideal
need not be assumed finitely presented.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]

/-- Algebra finite presentation persists for the actual coefficient quotient. -/
theorem algebraFinitePresentation_coefficient_ideal_quotient (I : Ideal B)
    [Algebra.FinitePresentation R (B ⧸ I)] :
    Algebra.FinitePresentation S ((S ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) :=
  Algebra.FinitePresentation.equiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S B S I)

/-- The actual finite branch supplies its own full ideal presentation. -/
theorem finitePresentation_ideal_of_finite_coefficient_branch
    [Algebra.FinitePresentation R B] (I : Ideal B)
    [Algebra.FinitePresentation R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (s : S ⊗[R] B)
    [Module.Finite S (Localization.Away s ⧸
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map
        (algebraMap (S ⊗[R] B) (Localization.Away s)))] :
    Module.FinitePresentation (Localization.Away s)
      ((I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map
        (algebraMap (S ⊗[R] B) (Localization.Away s))) := by
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let _ := algebraFinitePresentation_coefficient_ideal_quotient (R := R) (S := S) I
  let _ := flat_coefficient_ideal_quotient (R := R) (S := S) I
  let _ : Module.Finite S (Localization.Away (Ideal.Quotient.mk J s)) :=
    Module.Finite.equiv (localizedIdealQuotientEquiv (R := S) J s).symm.toLinearEquiv
  exact finitePresentation_ideal_on_finite_branch (R := S) J s

end FLT.Mazur.FCurve
