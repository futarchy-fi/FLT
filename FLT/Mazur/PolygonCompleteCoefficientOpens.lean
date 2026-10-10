/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCoefficientLine
public import FLT.Mazur.PolygonHomogeneousBoundaryEvaluation
public import FLT.Mazur.PolygonStageRetainedNaturality

/-!
# The original generator charts beneath the complete coefficient line

The chosen complete homogeneous coordinates evaluate to original boundary
sections. Their generator opens are precisely the inverse-image coordinate
charts, and therefore cover every original infinitesimal polygon stage.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family completeCoefficientCoordinates
  boundaryStageRetainedIso SectionRetainedProjConstruction.toProj Proj.map

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original evaluation map has the generator open of each homogeneous boundary section. -/
theorem originalStageToCompatibleProj_basicOpen (m d : ℕ) (hd : 0 < d)
    (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h))
    (hs : s ∈ compatibleVeroneseGrade K n h (exactVeroneseStep K n h) d) :
    originalStageToCompatibleProj K n h m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) s =
      sectionGeneratorOpen
        (tensorPower (boundaryLine K m n h) (exactVeroneseStep K n h * d))
        (homogeneousBoundarySection K n h m d s hs) := by
  rw [originalStageToCompatibleProj, Scheme.Hom.comp_preimage,
    boundaryVeroneseProjToCompatible_basicOpen, boundaryStageRetainedIso_hom,
    ← homogeneousBoundarySection_insertion K n h m d s hs]
  exact boundaryStageToExactVeroneseProj_basicOpen K n h m d hd _

/-- The tensor exponent seen by the chosen complete coefficient line. -/
def completeCoefficientBoundaryExponent : ℕ :=
  exactVeroneseStep K n h * (completeCoefficientCoordinates K n h).degree

/-- Each chosen complete coordinate evaluates to an actual section on the original stage. -/
def completeCoefficientBoundarySection (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    Γ(tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h), ⊤) :=
  homogeneousBoundarySection K n h m (completeCoefficientCoordinates K n h).degree
    ((completeCoefficientCoordinates K n h).coordinate i)
    ((completeCoefficientCoordinates K n h).homogeneous i)

/-- The chosen complete chart pulls back to the original boundary-section generator open. -/
theorem completeCoefficientChart_preimage (m : ℕ)
    (i : (completeCoefficientCoordinates K n h).Index) :
    originalStageToCompatibleProj K n h m ⁻¹ᵁ
        GradedProjLine.chart _ (completeCoefficientCoordinates K n h).coordinate i =
      sectionGeneratorOpen
        (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
        (completeCoefficientBoundarySection K n h m i) :=
  originalStageToCompatibleProj_basicOpen K n h m _
    (completeCoefficientCoordinates K n h).positive _
    ((completeCoefficientCoordinates K n h).homogeneous i)

/-- The evaluated coordinates generate the original boundary power everywhere on each stage. -/
theorem completeCoefficientBoundarySection_cover (m : ℕ) :
    (⨆ i, sectionGeneratorOpen
      (tensorPower (boundaryLine K m n h) (completeCoefficientBoundaryExponent K n h))
      (completeCoefficientBoundarySection K n h m i)) = ⊤ := by
  simp_rw [← completeCoefficientChart_preimage]
  rw [← Scheme.Hom.preimage_iSup]
  change originalStageToCompatibleProj K n h m ⁻¹ᵁ
    (⨆ i, Proj.basicOpen _ ((completeCoefficientCoordinates K n h).coordinate i)) = ⊤
  rw [(completeCoefficientCoordinates K n h).covers, Scheme.Hom.preimage_top]

/-- The actual boundary exponent is strictly positive. -/
theorem completeCoefficientBoundaryExponent_pos : 0 < completeCoefficientBoundaryExponent K n h :=
  Nat.mul_pos (exactVeroneseStep_pos K n h) (completeCoefficientCoordinates K n h).positive

end FLT.Mazur.PolygonInfinitesimalStages
