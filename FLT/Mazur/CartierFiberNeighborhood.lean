/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatIdealTensor
public import FLT.Mazur.FlatQuotientLocalCartier
public import FLT.Mazur.IdealCartierNeighborhood

/-!
# Spreading a coefficient-fiber Cartier equation

The local fiber criterion and finite presentation produce an actual principal
open neighborhood carrying a regular equation of the original ideal. The
localized ambient and quotient flatness are explicit algebraic hypotheses.
-/

@[expose] public noncomputable section
open TensorProduct IsLocalRing
namespace FLT.Mazur.FCurve

variable {R B A : Type*} [CommRing R] [IsLocalRing R] [CommRing B] [CommRing A]
  [Algebra B A] [Algebra R A] [IsLocalRing A] [IsLocalHom (algebraMap R A)]

/-- A regular residue-fiber ideal spreads to a Cartier neighborhood of the prime. -/
theorem cartier_neighborhood_of_coefficient_fiber (I : Ideal B)
    [Module.FinitePresentation B I] (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime A p] [Module.Flat R A]
    [Module.Flat R (A ⧸ I.map (algebraMap B A))]
    (hf : ∃ b : ResidueField R ⊗[R] A, IsRegular b ∧
      (I.map (algebraMap B A)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R)) =
          Ideal.span {b}) :
    ∃ s : B, s ∉ p ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let _ : Module.Flat B A := IsLocalization.flat A p.primeCompl
  let _ : Module.FinitePresentation A (I.map (algebraMap B A)) :=
    Module.FinitePresentation.of_equiv (flatIdealTensorEquiv I)
  obtain ⟨a, ha, hIa⟩ := exists_regular_generator_of_local_fiber
    (I.map (algebraMap B A)) hf
  exact ideal_regular_generator_spreads I p A a ha hIa

end FLT.Mazur.FCurve
