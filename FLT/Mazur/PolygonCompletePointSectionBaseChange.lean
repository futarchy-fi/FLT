/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointAcyclic
public import FLT.Mazur.CanonicalLineSectionBaseChange
public import FLT.Mazur.ProperLineSectionProjective

/-!
# Canonical universal base change for original point-power sections

The proved total-family acyclicity makes the actual sections finite projective.
Their canonical pullback map is bijective for every affine Cartesian square;
the map is the original adjunction-unit comparison, not a chosen basis map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback IncreasingCechCoefficients Chow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original positive point-power sections are finite over the original base's functions. -/
theorem completePointPower_sections_finite (i : Fin n) (m : ℕ) :
    Module.Finite Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) := by
  let _ : IsNoetherianRing Γ(Spec (.of (PowerSeries K)), ⊤) :=
    isNoetherianRing_of_ringEquiv (PowerSeries K)
      (Scheme.ΓSpecIso (.of (PowerSeries K))).commRingCatIsoToRingEquiv.symm
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := ((completePointLine_locallyFreeRankOne K n h i).tensorPower
    (m + 1)).isFinitePresentation
  exact LineSectionBaseChange.proper_sections_finite (exactVeroneseProjToBase K n h) _

/-- Original positive point-power sections are projective without choosing any coordinates. -/
theorem completePointPower_sections_projective (i : Fin n) (m : ℕ) :
    Module.Projective Γ(Spec (.of (PowerSeries K)), ⊤)
      (baseSections (tensorPower (completePointLine K n h i) (m + 1))
        (exactVeroneseProjToBase K n h).appTop.hom ⊤) := by
  let _ : IsNoetherianRing Γ(Spec (.of (PowerSeries K)), ⊤) :=
    isNoetherianRing_of_ringEquiv (PowerSeries K)
      (Scheme.ΓSpecIso (.of (PowerSeries K))).commRingCatIsoToRingEquiv.symm
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := exactVeroneseProjToBase_flat K n h
  exact LineSectionBaseChange.proper_acyclic_sections_projective
    (exactVeroneseProjToBase K n h) _
    ((completePointLine_locallyFreeRankOne K n h i).tensorPower (m + 1))
    (completePointPower_positive K n h i m)

variable {S Y : Scheme} [IsAffine S] (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The actual canonical global-section comparison is bijective on every affine square. -/
theorem completePointPower_globalComparison_bijective (i : Fin n) (m : ℕ) :
    Function.Bijective (globalComparison hs
      (tensorPower (completePointLine K n h i) (m + 1))) := by
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := exactVeroneseProjToBase_flat K n h
  exact LineSectionBaseChange.globalComparison_bijective (exactVeroneseProjToBase K n h) _
    ((completePointLine_locallyFreeRankOne K n h i).tensorPower (m + 1))
    (LineSectionBaseChange.positive_flat_of_vanishing (exactVeroneseProjToBase K n h) _
      (completePointPower_positive K n h i m)) hs

end FLT.Mazur.PolygonInfinitesimalStages
