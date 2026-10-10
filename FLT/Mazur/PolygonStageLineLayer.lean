/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageLayerSequence
public import FLT.Mazur.PolygonStageLineSectionFlat

/-!
# Closed coefficient layers of actual polygon tensor-line sections

On every affine open, the closed coefficient quotient embeds as the kernel
of adjacent parameter reduction. These sequences use the actual boundary
line sections and commute with their original open restriction maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback AffinePieceSectionLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (m n : ℕ) (h : 2 ≤ n) (d : ℕ)
  (U : (family R (m + 1) n h).left.Opens) (hU : IsAffineOpen U)

/-- The exact coefficient sequence on actual boundary tensor-line sections. -/
def boundaryPowerLayerSequence : ShortComplex (ModuleCat (Ring R (m + 1))) :=
  let _ := boundaryPowerSections_flat R (m + 1) n h d U hU
  flatLayerSequence R m (boundaryPowerSections R (m + 1) n h d U)

/-- Local section exactness follows from the flatness of the actual family and line. -/
theorem boundaryPowerLayerSequence_shortExact :
    (boundaryPowerLayerSequence R m n h d U hU).ShortExact := by
  let _ := boundaryPowerSections_flat R (m + 1) n h d U hU
  exact flatLayerSequence_shortExact R m (boundaryPowerSections R (m + 1) n h d U)

/-- The actual closed-fiber section embeds as its last parameter multiple. -/
theorem boundaryPowerLayerSequence_f_mk (s : boundaryPowerSections R (m + 1) n h d U) :
    (boundaryPowerLayerSequence R m n h d U hU).f (Submodule.Quotient.mk s) =
      parameter R (m + 1) ^ (m + 1) • s := rfl

/-- Adjacent coefficient reduction takes the actual section class. -/
theorem boundaryPowerLayerSequence_g_apply (s : boundaryPowerSections R (m + 1) n h d U) :
    (boundaryPowerLayerSequence R m n h d U hU).g s = Submodule.Quotient.mk s := rfl

variable {U} {V : (family R (m + 1) n h).left.Opens} (hV : IsAffineOpen V) (i : U ≤ V)

/-- Restriction of actual tensor-line sections commutes with the closed-layer embeddings. -/
theorem boundaryPowerLayerSequence_restrict :
    let _ := boundaryPowerSections_flat R (m + 1) n h d U hU
    let _ := boundaryPowerSections_flat R (m + 1) n h d V hV
    let f := AffinePieceSectionLocalization.baseRestriction
      (tensorPower (boundaryLine R (m + 1) n h) d)
      (stageScalars R (m + 1) n h) i
    f.comp (boundaryPowerLayerSequence R m n h d V hV).f.hom =
      (boundaryPowerLayerSequence R m n h d U hU).f.hom.comp (closedLayerMap R m f) := by
  let _ := boundaryPowerSections_flat R (m + 1) n h d U hU
  let _ := boundaryPowerSections_flat R (m + 1) n h d V hV
  exact closedLayerInclusion_natural R m _

end FLT.Mazur.PolygonInfinitesimalStages
