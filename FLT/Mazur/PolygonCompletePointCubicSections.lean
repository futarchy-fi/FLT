/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionRingIso
public import FLT.Mazur.PolygonCompletePointSurjective
public import FLT.Mazur.SectionGradedLineGeneratorOpen

/-!
# The original cubic coordinates as intrinsic origin-line sections

The full section comparison descends the original normalized X, Y, Z triple.
Surjectivity identifies its generator opens with the original cubic charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "A" => originDivisorLine (W) 1
local notation "L" => completePointLine K n h i
local notation "e" => completePointOriginLineIso K n h i
local notation "T" => completePointProjectiveSections K n h i

/-- The original projective coordinate sections descend to the intrinsic origin tensor cube. -/
def completePointCubicSections (j : Fin 3) : Γ(tensorPower (A) 3, ⊤) :=
  ((completePointSectionPullback_bijective K n h i 3 ⊤).surjective (T j)).choose

/-- The descended coordinates pull back to the unchanged normalized pole triple. -/
theorem completePointCubicSections_pullback (j : Fin 3) :
    SectionGradedLinePullback.sectionMap (g) (e) 3 ⊤
      (completePointCubicSections K n h i j) = T j :=
  ((completePointSectionPullback_bijective K n h i 3 ⊤).surjective (T j)).choose_spec

/-- The intrinsic coordinate generator opens are exactly the original cubic affine charts. -/
theorem completePointCubicSections_generatorOpen (j : Fin 3) :
    sectionGeneratorOpen (tensorPower (A) 3) (completePointCubicSections K n h i j) =
      (integralCurveChart (W) j).opensRange := by
  apply completePointToIntegralCubic_preimage_injective K n h i
  dsimp only
  rw [← SectionGradedLinePullback.sectionMap_generatorOpen (g)
      (completePointOriginLine_rankOne K n h i 1) (e),
    completePointCubicSections_pullback, completePointToIntegralCubic_preimage_chart]
  rfl

/-- The descended coordinate opens are affine over the original complete base. -/
theorem completePointCubicSections_affine (j : Fin 3) :
    IsAffineOpen (sectionGeneratorOpen (tensorPower (A) 3)
      (completePointCubicSections K n h i j)) := by
  rw [completePointCubicSections_generatorOpen]
  exact isAffineOpen_opensRange (integralCurveChart (W) j)

/-- The intrinsic origin cube has a finite generating cover on the entire original cubic. -/
theorem completePointCubicSections_cover :
    ⨆ j, sectionGeneratorOpen (tensorPower (A) 3)
      (completePointCubicSections K n h i j) = ⊤ := by
  apply completePointToIntegralCubic_preimage_injective K n h i
  dsimp only
  rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top]
  simp_rw [← SectionGradedLinePullback.sectionMap_generatorOpen (g)
    (completePointOriginLine_rankOne K n h i 1) (e), completePointCubicSections_pullback]
  exact completePointProjectiveSections_cover K n h i

end FLT.Mazur.PolygonInfinitesimalStages
