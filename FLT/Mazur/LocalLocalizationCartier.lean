/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StandardSmoothFiniteSupportCartier
public import FLT.Mazur.CartierIdealStalkNeighborhood

/-!
# Cartier equations in arbitrary local localizations

A localization that is a local ring is the prime localization at the
contraction of its maximal ideal. This lets finite-support Cartier equations
on smooth field charts pass to any actual local realization of that chart.
-/

@[expose] public noncomputable section
open IsLocalRing
universe u
namespace FLT.Mazur.FCurve

variable {B L : Type*} [CommRing B] [CommRing L] [Algebra B L] [IsLocalRing L]

/-- A local localization is a localization at its contracted maximal ideal. -/
theorem local_localization_atPrime (M : Submonoid B) [IsLocalization M L] :
    IsLocalization.AtPrime L ((maximalIdeal L).comap (algebraMap B L)) := by
  apply IsLocalization.of_le (M := M)
  · intro m hm
    exact (notMem_maximalIdeal.mpr
      (IsLocalization.map_units L (⟨m, hm⟩ : M)))
  · intro b hb
    exact notMem_maximalIdeal.mp hb

/-- Regular local equations of a standard smooth field chart transport to any
local localization, including coefficient fibers of ambient local rings. -/
theorem regular_generator_local_localization
    {K B L : Type u} [Field K] [CommRing B] [CommRing L] [Algebra K B]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K B]
    [Algebra B L] [IsLocalRing L] (M : Submonoid B) [IsLocalization M L]
    (I : Ideal B) [IsArtinianRing (B ⧸ I)] :
    ∃ a : L, IsRegular a ∧ I.map (algebraMap B L) = Ideal.span {a} := by
  let p := (maximalIdeal L).comap (algebraMap B L)
  let _ : IsLocalization.AtPrime L p := local_localization_atPrime M
  obtain ⟨a, ha, hIa⟩ := regular_generator_standardSmooth_artinian_support (K := K) I p
  exact regular_generator_localization_transport p.primeCompl I a ha hIa

end FLT.Mazur.FCurve
