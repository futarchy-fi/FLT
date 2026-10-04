/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedGeneratorLocalization

/-!
# Homogeneous fractions as functions on generator opens

Restrict the full section ring to the actual generator open, then identify
its degree-zero localization with the structure-sheaf sections. This defines
the chart comparison without choosing coordinates for the original line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedChartComparison
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) [Fact (LocallyFreeRankOne L)]

/-- Restriction preserves every tensor degree of the full section ring. -/
def gradedRestriction (U : X.Opens) : grade L ⊤ →+*ᵍ grade L U where
  __ := restrictRingHom L U U.leTop
  map_mem := by
    rintro n a ⟨t, rfl⟩
    exact ⟨_, (restrict_of L U.leTop n t).symm⟩

variable (d : ℕ) (s : Piece L ⊤ d) (U : X.Opens)
  (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s)

/-- The actual homogeneous-localization-to-functions comparison on a generator subopen. -/
def toFunctions : Away (grade L ⊤) (of L ⊤ d s) →+* Γ(X, U) :=
  (SectionGradedGeneratorLocalization.scalarEquiv L d s U hU).symm.toRingHom.comp
    (Away.map (gradedRestriction L U) (of L ⊤ d s))

/-- Comparison satisfies the intrinsic homogeneous numerator-denominator equation. -/
lemma toFunctions_mk_smul (n : ℕ) (a : SectionGradedSum.Sections L ⊤)
    (ha : a ∈ grade L ⊤ (n • d)) :
    toFunctions L d s U hU (Away.mk (grade L ⊤) ⟨s, rfl⟩ n a ha) •
      (restrictRingHom L U U.leTop (of L ⊤ d s)) ^ n = restrictRingHom L U U.leTop a := by
  unfold toFunctions
  rw [RingHom.comp_apply]
  erw [Away.map_mk]
  exact HomogeneousLocalizationGenerator.scalarEquiv_symm_mk_smul (grade L U)
    _ (SectionGradedGeneratorLocalization.power_smul_injective L d s U hU)
    (SectionGradedGeneratorLocalization.power_generates L d s U hU) n _ _

end FLT.Mazur.SectionGradedChartComparison
