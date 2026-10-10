/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerReesSections
public import FLT.Mazur.AffineChartSectionLocalization
public import FLT.Mazur.DirectSumLocalization

/-!
# Simultaneous localization of all actual power sections

Over an affine chart, the direct sum of the original ideal-power sheaves
localizes on every principal open. Finite degree support gives a single
denominator, and a single annihilating power, for each total section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.GlobalIdealPower
open scoped DirectSum

universe u

namespace FLT.Mazur.IdealPowerRees

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation] (V : X.affineOpens)

/-- The actual power sections on a subopen, with scalars from the fixed chart. -/
abbrev chartSections (W : X.Opens) (h : W ≤ V.1) : ModuleCat Γ(X, V.1) :=
  ModuleCat.of Γ(X, V.1)
    (⨁ n : ℕ, AffineChartSectionLocalization.sections (power I n M) V W h)

/-- The direct sum of the original restriction maps over the chart coordinate ring. -/
def chartRestriction {W T : X.Opens} (hW : W ≤ V.1) (hT : T ≤ V.1) (i : W ⟶ T) :
    chartSections I M V T hT →ₗ[Γ(X, V.1)] chartSections I M V W hW :=
  DirectSum.lmap (fun n ↦ AffineChartSectionLocalization.restriction
    (power I n M) V hW hT i)

omit [IsLocallyNoetherian X] [M.IsFinitePresentation] in
/-- Every component is the original ideal-power section restriction. -/
lemma chartRestriction_apply {W T : X.Opens} (hW : W ≤ V.1) (hT : T ≤ V.1)
    (i : W ⟶ T) (s : chartSections I M V T hT) (n : ℕ) :
    chartRestriction I M V hW hT i s n = (power I n M).presheaf.map i.op (s n) := rfl

/-- The complete direct sum localizes, with no fixed upper bound on its exponents. -/
theorem chartRestriction_isLocalized (r : Γ(X, V.1)) :
    IsLocalizedModule.Away r (chartRestriction I M V (X.basicOpen_le r) le_rfl
      (homOfLE (X.basicOpen_le r))) := by
  have (n : ℕ) := AffineChartSectionLocalization.restriction_isLocalized (power I n M) V r
  exact DirectSumLocalization.isLocalizedModule r _

/-- One chart-scalar power clears denominators in every degree of a local section. -/
theorem chartRestriction_exists_numerator (r : Γ(X, V.1))
    (s : chartSections I M V (X.basicOpen r) (X.basicOpen_le r)) :
    ∃ (n : ℕ) (t : chartSections I M V V.1 le_rfl), r ^ n • s =
      chartRestriction I M V (X.basicOpen_le r) le_rfl
        (homOfLE (X.basicOpen_le r)) t := by
  let _ := chartRestriction_isLocalized I M V r
  exact IsLocalizedModule.Away.surj _ r s

/-- Vanishing after restriction is killed by one power on the entire finite support. -/
theorem chartRestriction_exists_annihilator (r : Γ(X, V.1))
    (s : chartSections I M V V.1 le_rfl)
    (hs : chartRestriction I M V (X.basicOpen_le r) le_rfl
      (homOfLE (X.basicOpen_le r)) s = 0) : ∃ n : ℕ, r ^ n • s = 0 := by
  let _ := chartRestriction_isLocalized I M V r
  have hz : chartRestriction I M V (X.basicOpen_le r) le_rfl
      (homOfLE (X.basicOpen_le r)) s =
        chartRestriction I M V (X.basicOpen_le r) le_rfl
          (homOfLE (X.basicOpen_le r)) 0 := hs.trans (map_zero _).symm
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r hz
  exact ⟨n, hn.trans (smul_zero _)⟩

end FLT.Mazur.IdealPowerRees
