/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedSmoothFiniteFlatCartier

/-!
# Local equations through an intermediate smooth localization

The final local ring may be any realization of a localization, including an
actual scheme stalk. Finiteness is required only on the original quotient;
the intermediate smooth chart can lose finiteness over the local base.
-/

@[expose] public noncomputable section
open TensorProduct IsLocalRing
universe u
namespace FLT.Mazur.FCurve
variable {R B D A : Type u} [CommRing R] [IsLocalRing R]
  [CommRing B] [CommRing D] [CommRing A] [IsLocalRing A]
  [Algebra R B] [Algebra R D] [Algebra R A]
  [Algebra B D] [Algebra B A] [Algebra D A]
  [IsScalarTower R B D] [IsScalarTower R B A]
  [IsScalarTower R D A] [IsScalarTower B D A]
  [Algebra.FinitePresentation R B] [Algebra.IsStandardSmoothOfRelativeDimension 1 R D]
  [IsLocalHom (algebraMap R A)]

/-- Construct the regular equation in an arbitrary local realization of the ambient. -/
theorem regular_generator_through_localized_smooth_chart
    (M : Submonoid B) [IsLocalization M D]
    (L : Submonoid B) [IsLocalization L A]
    (N : Submonoid D) [IsLocalization N A]
    (I : Ideal B) [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)] :
    ∃ a : A, IsRegular a ∧ I.map (algebraMap B A) = Ideal.span {a} := by
  let _ : Algebra.IsStandardSmooth R D :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ : Module.Flat D A := IsLocalization.flat A N
  let _ : Module.Flat R A := Module.Flat.trans R D A
  let _ : Module.Flat B A := IsLocalization.flat A L
  let _ := ideal_finitePresentation_of_local_finite_flat (R := R) I
  let J := I.map (algebraMap B A)
  let _ : Module.FinitePresentation A J :=
    Module.FinitePresentation.of_equiv (flatIdealTensorEquiv I)
  let _ : Module.Flat (B ⧸ I) (A ⧸ J) := IsLocalization.flat _
    (Algebra.algebraMapSubmonoid (B ⧸ I) L)
  let _ : IsScalarTower R (B ⧸ I) (A ⧸ J) := .to₁₃₄ R B _ _
  let _ : Module.Flat R (A ⧸ J) := Module.Flat.trans R (B ⧸ I) (A ⧸ J)
  let _ := artinian_coefficient_quotient_of_localization
    (R := R) (K := ResidueField R) (D := D) M I
  have hf := regular_generator_coefficient_fiber_of_artinian
    (R := R) (A := A) N (I.map (algebraMap B D))
  have he : (I.map (algebraMap B D)).map (algebraMap D A) = J := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B D A]
  rw [he] at hf
  exact exists_regular_generator_of_local_fiber (R := R) J hf

end FLT.Mazur.FCurve
