/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedChartComparison

/-!
# Intrinsic fraction formulas and restriction of the chart comparison

A homogeneous fraction is the regular ratio of its numerator to the actual
power section. This description makes restriction compatibility explicit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedChartRatios
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
open SectionGradedPowerRatios SectionGradedChartComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]
  (d : ℕ) (s : Piece L ⊤ d)

/-- The chart comparison is the actual ratio with the corresponding power section. -/
lemma toFunctions_eq_coefficient (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) (n : ℕ)
    (t : Piece L ⊤ (d * n)) (ht : of L ⊤ (d * n) t ∈ grade L ⊤ (n • d)) :
    toFunctions L d s U hU (Away.mk (grade L ⊤) ⟨s, rfl⟩ n (of L ⊤ (d * n) t) ht) =
      coefficient L hL.out d s n U hU t := by
  apply SectionGradedGeneratorLocalization.power_smul_injective L d s U hU n
  exact (toFunctions_mk_smul L d s U hU n _ ht).trans
    (coefficient_smul L hL.out d s n U hU t).symm

/-- Every homogeneous fraction compares naturally under restriction of generator opens. -/
lemma toFunctions_restrict {U V : X.Opens} (hVU : V ≤ U)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) :
    (X.presheaf.map (homOfLE hVU).op).hom.comp (toFunctions L d s U hU) =
      toFunctions L d s V (hVU.trans hU) := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grade L ⊤)
    (show of L ⊤ d s ∈ grade L ⊤ d from ⟨s, rfl⟩) z
  have ha' : a ∈ grade L ⊤ (d * n) := by
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_comm] using ha
  obtain ⟨t, rfl⟩ := ha'
  rw [RingHom.comp_apply, toFunctions_eq_coefficient, toFunctions_eq_coefficient]
  exact coefficient_restrict L hL.out d s n hVU hU t

end FLT.Mazur.SectionGradedChartRatios
