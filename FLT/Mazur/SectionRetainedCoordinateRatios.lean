/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedChartComparison
public import FLT.Mazur.GradedProjLineCoordinates

/-!
# Retained homogeneous coordinates evaluate to original section ratios

The fraction with numerator and denominator in the same retained degree
evaluates to their actual ratio in the original boundary tensor power.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace FLT.Mazur.SectionRetainedCoordinateRatios

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  (d : ℕ) (s t : Γ(tensorPower L (q * d), ⊤))

/-- A retained ratio is the same original numerator and denominator in the full section ring. -/
theorem inclusion_ratio :
    RetainedSubringLocalization.inclusion (grade L ⊤) q (insertion L q d s)
        (Away.mk _ (insertion_mem L q d s) 1 (insertion L q d t)
          (by simpa only [one_smul] using insertion_mem L q d t)) =
      Away.mk (grade L ⊤) (show of L ⊤ (q * d) s ∈ grade L ⊤ (q * d) from ⟨s, rfl⟩)
        1 (of L ⊤ (q * d) t) (by simpa only [one_smul] using
          (show of L ⊤ (q * d) t ∈ grade L ⊤ (q * d) from ⟨t, rfl⟩)) := by
  apply val_injective
  rw [RetainedSubringLocalization.inclusion_val, Away.val_mk, Away.val_mk]
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

/-- The intrinsic retained function comparison is the actual same-degree section ratio. -/
theorem toFunctions_ratio (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s) :
    toFunctions L q d s U hU
        (Away.mk _ (insertion_mem L q d s) 1 (insertion L q d t)
          (by simpa only [one_smul] using insertion_mem L q d t)) =
      sectionRatioOn (tensorPower L (q * d)) s U hU t := by
  rw [toFunctions, RingHom.comp_apply]
  erw [inclusion_ratio L q d s t]
  symm
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  apply DirectSum.of_injective (β := SectionGradedMultiplication.Piece L U) (q * d)
  change of L U (q * d) (_ • _) = of L U (q * d) _
  rw [map_smul]
  have he := SectionGradedChartComparison.toFunctions_mk_smul L (q * d) s U hU
    1 (of L ⊤ (q * d) t) (by simpa only [one_smul] using
      (show of L ⊤ (q * d) t ∈ grade L ⊤ (q * d) from ⟨t, rfl⟩))
  change _ • (restrict L U.leTop (of L ⊤ (q * d) s)) ^ 1 =
    restrict L U.leTop (of L ⊤ (q * d) t) at he
  simp only [pow_one, restrict_of] at he
  exact he

end FLT.Mazur.SectionRetainedCoordinateRatios
