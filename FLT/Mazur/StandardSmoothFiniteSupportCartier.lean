/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteSupportCartier
public import FLT.Mazur.SectionDivisors
public import FLT.Mazur.IdealCartierNeighborhood
public import Mathlib.RingTheory.Jacobson.Artinian

/-!
# Cartier neighborhoods in standard smooth curves over fields

Standard smooth dimension one constructs the étale coordinate needed by the
finite-support criterion. Artinian quotients are finite over the field, and
Noetherian finite presentation spreads the resulting regular local equations.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FCurve

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]
  [hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 1 K B]

/-- Regular local equations for finite subschemes in a standard smooth curve chart. -/
theorem regular_generator_standardSmooth_finite_support
    (I : Ideal B) [Module.Finite K (B ⧸ I)] (q : Ideal B) [q.IsPrime] :
    ∃ a : Localization.AtPrime q, IsRegular a ∧
      I.map (algebraMap B (Localization.AtPrime q)) = Ideal.span {a} := by
  obtain ⟨g, hg⟩ := exists_etale_polynomial_coordinate (R := K) (B := B)
  exact regular_generator_etale_finite_support g hg I q

include hSmooth in
/-- The finite-dimensional hypothesis follows from Artinianness in a smooth chart. -/
theorem regular_generator_standardSmooth_artinian_support
    (I : Ideal B) [IsArtinianRing (B ⧸ I)] (q : Ideal B) [q.IsPrime] :
    ∃ a : Localization.AtPrime q, IsRegular a ∧
      I.map (algebraMap B (Localization.AtPrime q)) = Ideal.span {a} := by
  let _ : Algebra.IsStandardSmooth K B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ : Module.Finite K (B ⧸ I) := (Module.finite_iff_isArtinianRing K (B ⧸ I)).mpr inferInstance
  exact regular_generator_standardSmooth_finite_support (K := K) I q

include hSmooth in
/-- Every point has a principal Cartier neighborhood for an Artinian quotient. -/
theorem cartier_neighborhood_standardSmooth_artinian_support
    (I : Ideal B) [IsArtinianRing (B ⧸ I)] (q : Ideal B) [q.IsPrime] :
    ∃ s : B, s ∉ q ∧ ∃ a : Localization.Away s, IsRegular a ∧
      I.map (algebraMap B (Localization.Away s)) = Ideal.span {a} := by
  let _ : Algebra.IsStandardSmooth K B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  let _ : Module.FinitePresentation B I := Module.finitePresentation_of_finite B I
  obtain ⟨a, ha, hIa⟩ := regular_generator_standardSmooth_artinian_support (K := K) I q
  exact ideal_regular_generator_spreads I q (Localization.AtPrime q) a ha hIa

end FLT.Mazur.FCurve
