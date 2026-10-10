/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArtinianCoefficientFiberCartier
public import FLT.Mazur.ArtinianLocalizedCoefficientQuotient
public import FLT.Mazur.FiniteFlatLocalIdealPresentation
public import FLT.Mazur.CartierFiberNeighborhood
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Cartier neighborhoods through localized smooth charts

The finite flat family is retained on its original finitely presented affine
ambient. An intermediate smooth chart may be any localization: no finiteness
of the restricted family over the base is asserted or required. Its residue
fiber is Artinian by tensor localization, while ideal finite presentation and
quotient flatness come from the original ambient. The resulting equation
spreads to a principal neighborhood in that original ambient.
-/

@[expose] public noncomputable section
open TensorProduct IsLocalRing
universe u
namespace FLT.Mazur.FCurve
variable {R B D : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [CommRing D]
  [Algebra R B] [Algebra R D] [Algebra B D] [IsScalarTower R B D]
  [Algebra.FinitePresentation R B] [Algebra.IsStandardSmoothOfRelativeDimension 1 R D]

/-- A localized smooth chart supplies Cartier equations without a finite chart quotient. -/
theorem cartier_neighborhood_through_localized_smooth_chart
    (M : Submonoid B) [IsLocalization M D] (I : Ideal B)
    [Module.Finite R (B ⧸ I)] [Module.Flat R (B ⧸ I)] (q : Ideal B) [q.IsPrime]
    [Algebra D (Localization.AtPrime q)] [IsScalarTower B D (Localization.AtPrime q)]
    [IsScalarTower R D (Localization.AtPrime q)]
    [IsLocalHom (algebraMap R (Localization.AtPrime q))]
    (N : Submonoid D) [IsLocalization N (Localization.AtPrime q)] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let A := Localization.AtPrime q
  let _ : Algebra.IsStandardSmooth R D :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ : Module.Flat D A := IsLocalization.flat A N
  let _ : Module.Flat R A := Module.Flat.trans R D A
  let _ := ideal_finitePresentation_of_local_finite_flat (R := R) I
  let J := I.map (algebraMap B A)
  let _ : Module.Flat (B ⧸ I) (A ⧸ J) := IsLocalization.flat _
    (Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl)
  let _ : IsScalarTower R (B ⧸ I) (A ⧸ J) := .to₁₃₄ R B _ _
  let _ : Module.Flat R (A ⧸ J) := Module.Flat.trans R (B ⧸ I) (A ⧸ J)
  let _ := artinian_coefficient_quotient_of_localization
    (R := R) (K := ResidueField R) (D := D) M I
  obtain ⟨a, ha, hIa⟩ := regular_generator_coefficient_fiber_of_artinian
    (R := R) (A := A) N (I.map (algebraMap B D))
  have he : (I.map (algebraMap B D)).map (algebraMap D A) = J := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B D A]
  rw [he] at hIa
  exact cartier_neighborhood_of_coefficient_fiber (R := R) (A := A) I q ⟨a, ha, hIa⟩

end FLT.Mazur.FCurve
