/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatLocalIdealPresentation
public import FLT.Mazur.StandardSmoothLocalCartier

/-!
# Cartier neighborhoods for finite flat ideals on smooth local-base charts

The ambient smooth presentation and the finite flat quotient now construct
finite presentation of the full ideal. Together with the constructed residue
fiber equation, this removes the additional ideal-presentation hypothesis
from the standard smooth curve criterion over every local base ring.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FCurve
variable {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [Algebra R B]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]

/-- Construct a Cartier neighborhood from smoothness and the finite flat quotient alone. -/
theorem cartier_neighborhood_standardSmooth_finite_flat_unconditional
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (q : Ideal B) [q.IsPrime]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let _ : Algebra.IsStandardSmooth R B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ := ideal_finitePresentation_of_local_finite_flat (R := R) I
  exact cartier_neighborhood_standardSmooth_finite_flat (R := R) I q

end FLT.Mazur.FCurve
