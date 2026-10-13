/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSectionFree
public import FLT.Mazur.SectionPoleAdaptedBasis
public import FLT.Mazur.SectionPoleMultiplicativeCoordinates

/-!
# Integral frames and normalized lifts for the original point filtration

The actual pole line over the complete local base is invertible and free.
Choosing its frame therefore constructs normalized integral leading lifts;
no group law or smoothness of the whole polygon is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve FCurve.ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A single frame of the point line restricted to its original marking. -/
def completePointSectionFrame (i : Fin n) :
    (Scheme.Modules.pullback (completeBaseMarking K n h i)).obj
      (completePointLine K n h i) ≅ structureModule (Spec (.of (PowerSeries K))) := by
  let L := (Scheme.Modules.pullback (completeBaseMarking K n h i)).obj
    (completePointLine K n h i)
  have hL : LocallyFreeRankOne L :=
    (completePointLine_locallyFreeRankOne K n h i).pullback _
  let _ := hL.isFinitePresentation
  let _ := completeBase_sections_local K
  let _ := SchemePicard.sections_invertible L hL
  let _ : Module.Flat Γ(Spec (.of (PowerSeries K)), ⊤) Γ(L, ⊤) :=
    Module.Flat.of_projective
  let _ : Module.Free Γ(Spec (.of (PowerSeries K)), ⊤) Γ(L, ⊤) :=
    Module.free_of_flat_of_isLocalRing
  let _ := (structureModule_locallyFreeRankOne
    (X := Spec (.of (PowerSeries K)))).isFinitePresentation
  exact SchemePicard.isoOfSections
    (Module.Invertible.free_iff_linearEquiv.mp inferInstance).some

/-- Every integral pole-line frame uses powers of the same section-line frame. -/
def completePointPoleFrame (i : Fin n) (m : ℕ) :
    Γ(sectionPoleLine (completeBaseMarking K n h i)
      (completeBaseMarking_relativeCartier K n h i).1 m, ⊤) ≃ₗ[
        Γ(Spec (.of (PowerSeries K)), ⊤)] Γ(Spec (.of (PowerSeries K)), ⊤) :=
  sectionPoleMultiplicativeCoordinates (completeBaseMarking K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 (completePointSectionFrame K n h i) m

/-- A positive pole step has an integral lift with prescribed leading coefficient one. -/
def completePointPoleLift (i : Fin n) (m : ℕ) :
    ModuleRingH (exactVeroneseProjToBase K n h).appTop.hom
      (tensorPower (completePointLine K n h i) (m + 2)) 0 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (m + 1)) 1) :=
    completePointPower_positive K n h i m 0
  exact sectionPoleNormalizedLift (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 (m + 1)
    (completePointPoleFrame K n h i (m + 2))

/-- The constructed lift has coefficient one for the original divisor leading map. -/
theorem completePointPoleLift_leading (i : Fin n) (m : ℕ) :
    let _ := exactVeroneseProjToBase_isProper K n h
    completePointPoleFrame K n h i (m + 2)
      (sectionPoleLeading (exactVeroneseProjToBase K n h)
        (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
        (completeBaseMarking_relativeCartier K n h i).1 (m + 1)
        (completePointPoleLift K n h i m)) = 1 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : Subsingleton (ModuleH (tensorPower
      (divisorLineBundle (completeBaseMarking K n h i).ker
        (completeBaseMarking_relativeCartier K n h i).1) (m + 1)) 1) :=
    completePointPower_positive K n h i m 0
  exact sectionPoleNormalizedLift_leading (exactVeroneseProjToBase K n h)
    (completeBaseMarking K n h i) (completeBaseMarking_toBase K n h i)
    (completeBaseMarking_relativeCartier K n h i).1 (m + 1)
    (completePointPoleFrame K n h i (m + 2))

end FLT.Mazur.PolygonInfinitesimalStages
