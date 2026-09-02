/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import FLT.AINTLIB.DedekindResidue.ExplicitFormula.TestFunction
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally complex Weil--Poitou explicit-formula interface

This file is the M7--M8 seam in the Odlyzko endgame.  It records the totally complex
specialization of AINTLIB's `weil_explicit_formula_auxF`: the pole values are explicit,
the archimedean coefficients use `r1 = 0`, and the prime side has its fixed negative sign.

The identity is deliberately supplied as a hypothesis.  Replacing that hypothesis by the
eventual port of `weil_explicit_formula_auxF` should therefore only change this seam.
-/

@[expose] public section

open Module NumberField

namespace Odlyzko

universe u

/--
The Weil--Poitou identity in the form consumed by the totally complex Odlyzko endgame.

`zeroSide` is the limiting zero-capture sum, `phi` is the transform evaluated at the two
poles, `archimedeanIntegral` is the `sinh` integral, and `primeSide` is `H(0)`.  The factors
of the degree are the `r1 = 0` specialization of AINTLIB's formula: `2 * r2 = [K : Q]`.
-/
structure TotallyComplexExplicitFormula
    (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℂ) (phi : ℂ → ℂ)
    (zeroSide archimedeanIntegral primeSide : ℂ) : Prop where
  admissible : DedekindResidue.IsAdmissibleTestFn F
  formula :
    zeroSide =
      (phi 0 + phi 1)
        + ((Real.log |(discr K : ℝ)| : ℝ) : ℂ) * F 0
        - ((finrank ℚ K : ℕ) : ℂ)
            * ((Real.eulerMascheroniConstant + Real.log (8 * Real.pi) : ℝ) : ℂ) * F 0
        + ((finrank ℚ K : ℕ) : ℂ) * archimedeanIntegral
        - (primeSide + primeSide)

/--
Package an assumed Weil--Poitou identity as the M7--M8 interface.  In particular, the
analytic formula is an explicit argument rather than an unproved theorem declaration.
-/
theorem totallyComplexExplicitFormula_of_hypothesis
    (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
    (F : ℝ → ℂ) (phi : ℂ → ℂ)
    (zeroSide archimedeanIntegral primeSide : ℂ)
    (hF : DedekindResidue.IsAdmissibleTestFn F)
    (hformula :
      zeroSide =
        (phi 0 + phi 1)
          + ((Real.log |(discr K : ℝ)| : ℝ) : ℂ) * F 0
          - ((finrank ℚ K : ℕ) : ℂ)
              * ((Real.eulerMascheroniConstant + Real.log (8 * Real.pi) : ℝ) : ℂ) * F 0
          + ((finrank ℚ K : ℕ) : ℂ) * archimedeanIntegral
          - (primeSide + primeSide)) :
    TotallyComplexExplicitFormula K F phi zeroSide archimedeanIntegral primeSide :=
  ⟨hF, hformula⟩

end Odlyzko
