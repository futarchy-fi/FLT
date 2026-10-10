/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedCoefficientFiberCartier
public import FLT.Mazur.CartierFiberNeighborhood
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Lifting finite flat subschemes in standard smooth curve charts

For a local base, the actual residue fiber supplies its own regular equation.
Smoothness gives ambient flatness, and localization preserves quotient flatness.
Finite presentation of the ideal then lifts and spreads the equation. No
Noetherian-base assumption is used; ideal finite presentation remains explicit.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FCurve

variable {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]

/-- A finite flat quotient on a smooth chart has Cartier neighborhoods when its
ideal is finitely presented; the fiber equation and both flatness witnesses are constructed. -/
theorem cartier_neighborhood_standardSmooth_finite_flat
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    [Module.FinitePresentation B I] (q : Ideal B) [q.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let A := Localization.AtPrime q
  let _ : Algebra.IsStandardSmooth R B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ : Module.Flat R A := Module.Flat.trans R B A
  let J := I.map (algebraMap B A)
  let _ : Module.Flat (B ⧸ I) (A ⧸ J) := IsLocalization.flat _
    (Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl)
  let _ : IsScalarTower R (B ⧸ I) (A ⧸ J) := .to₁₃₄ R B _ _
  let _ : Module.Flat R (A ⧸ J) := Module.Flat.trans R (B ⧸ I) (A ⧸ J)
  exact cartier_neighborhood_of_coefficient_fiber (R := R) (A := A) I q
    (regular_generator_localized_coefficient_fiber (R := R) q.primeCompl I)

end FLT.Mazur.FCurve
