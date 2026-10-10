/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PresentedFiniteCoefficientBranch
public import FLT.Mazur.SpectrumSmoothFiniteFlatCartier
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Cartier equations on finite branches after coefficient change

The finite branch has smooth curve coordinates, a flat presented quotient,
and hence an actual Cartier ideal sheaf. With etale coefficients its map to
the original ambient is etale, as required for neighborhood descent.
-/

@[expose] public noncomputable section
open TensorProduct CategoryTheory AlgebraicGeometry
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]

/-- A principal coefficient branch is etale over the original ambient for etale coefficients. -/
theorem etale_coefficient_branch [Algebra.Etale R S] (s : S ⊗[R] B) :
    Algebra.Etale B (Localization.Away s) := by
  let T := S ⊗[R] B
  let E : (B ⊗[R] S) ≃ₐ[B] T :=
    { __ := Algebra.TensorProduct.comm R B S, commutes' _ := rfl }
  let _ : Algebra.Etale B T := Algebra.Etale.of_equiv E
  exact Algebra.Etale.comp B T (Localization.Away s)

/-- The actual finite branch of a flat family on smooth coordinates is Cartier. -/
theorem effectiveCartier_finite_coefficient_branch
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
    (I : Ideal B) [Algebra.FinitePresentation R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (s : S ⊗[R] B)
    [Module.Finite S (Localization.Away s ⧸
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map
        (algebraMap (S ⊗[R] B) (Localization.Away s)))] :
    EffectiveCartier (BaseAdicThickening.baseIdeal (.of (Localization.Away s))
      ((I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map
        (algebraMap (S ⊗[R] B) (Localization.Away s)))) := by
  let T := S ⊗[R] B
  let D := Localization.Away s
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  let K := J.map (algebraMap T D)
  let _ := algebraFinitePresentation_coefficient_ideal_quotient (R := R) (S := S) I
  let _ := flat_coefficient_ideal_quotient (R := R) (S := S) I
  let E := localizedIdealQuotientEquiv (R := S) J s
  let _ : Algebra.FinitePresentation S (D ⧸ K) := Algebra.FinitePresentation.equiv E
  let _ : Module.Flat S (D ⧸ K) := Module.Flat.of_linearEquiv E.toLinearEquiv.symm
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 0 T D :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away s
  let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 S D :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans (n := 1) (m := 0) S T D
  exact effectiveCartier_baseIdeal_of_smooth_finite_flat (R := S) K

end FLT.Mazur.FCurve
