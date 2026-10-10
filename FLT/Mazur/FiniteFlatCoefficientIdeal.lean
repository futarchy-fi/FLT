/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatLocalIdealPresentation
public import FLT.Mazur.FlatIdealTensor
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The full ideal after local coefficient change

A finite flat quotient remains finite flat after coefficient change. If the
new coefficient ring is local, its actual extended ideal is finitely presented.
Any further flat ambient extension preserves this ideal presentation.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.FCurve
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B]

/-- Coefficient change preserves finiteness of the actual quotient. -/
theorem finite_coefficient_ideal_quotient (I : Ideal B) [Module.Finite R (B ⧸ I)] :
    Module.Finite S ((S ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) :=
  Module.Finite.equiv (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S B S I).toLinearEquiv

/-- Coefficient change preserves flatness of the actual quotient. -/
theorem flat_coefficient_ideal_quotient (I : Ideal B) [Module.Flat R (B ⧸ I)] :
    Module.Flat S ((S ⊗[R] B) ⧸
      I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) :=
  Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S B S I).toLinearEquiv.symm

/-- Local coefficient change constructs a presentation of the full extended ideal. -/
theorem finitePresentation_local_coefficient_ideal [IsLocalRing S]
    [Algebra.FinitePresentation R B] (I : Ideal B)
    [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)] :
    Module.FinitePresentation (S ⊗[R] B)
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) := by
  let _ := finite_coefficient_ideal_quotient (R := R) (S := S) I
  let _ := flat_coefficient_ideal_quotient (R := R) (S := S) I
  exact ideal_finitePresentation_of_local_finite_flat (R := S) _

/-- A subsequent flat ambient extension retains the constructed ideal presentation. -/
theorem finitePresentation_local_coefficient_ideal_map [IsLocalRing S]
    [Algebra.FinitePresentation R B] (I : Ideal B)
    [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)]
    (A : Type u) [CommRing A] [Algebra (S ⊗[R] B) A]
    [Module.Flat (S ⊗[R] B) A] :
    Module.FinitePresentation A
      ((I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map
        (algebraMap (S ⊗[R] B) A)) := by
  let _ := finitePresentation_local_coefficient_ideal (R := R) (S := S) I
  exact Module.FinitePresentation.of_equiv (flatIdealTensorEquiv _)

end FLT.Mazur.FCurve
