/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointProjectiveSections
public import FLT.Mazur.SectionPoleCanonicalCoefficient

/-!
# The original complete-base homogeneous coordinates along the marking

The original homogeneous coordinates restrict to [0, 1, 0] in the retained marking frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "e" => completePointSectionFrame K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
/-- The included order-two coordinate vanishes along the original marking. -/
theorem completePointProjectiveX_coefficient :
    sectionPoleCoefficient (s) hI e 3 (completePointProjectiveX K n h i) = 0 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact sectionPoleCoefficient_step (f) (s) (completeBaseMarking_toBase K n h i) hI e 2
    (completePointPoleLift K n h i 0)

/-- The actual order-three coordinate equals one in the retained marking frame. -/
theorem completePointProjectiveY_coefficient :
    sectionPoleCoefficient (s) hI e 3 (completePointProjectiveY K n h i) = 1 :=
  completePointPoleLift_coefficient K n h i 1

/-- The canonical degree-three coordinate vanishes along the original marking. -/
theorem completePointProjectiveZ_coefficient :
    sectionPoleCoefficient (s) hI e 3 (completePointProjectiveZ K n h i) = 0 := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact sectionPoleCoefficient_canonical (f) (s) (completeBaseMarking_toBase K n h i) hI e 2

/-- The full original coordinate triple restricts to [0, 1, 0] over the actual base. -/
theorem completePointProjectiveSections_coefficient (j : Fin 3) :
    sectionPoleCoefficient (s) hI e 3 (T j) = (![0, 1, 0] : Fin 3 → Γ(S, ⊤)) j := by
  fin_cases j
  · exact completePointProjectiveX_coefficient K n h i
  · exact completePointProjectiveY_coefficient K n h i
  · exact completePointProjectiveZ_coefficient K n h i

end FLT.Mazur.PolygonInfinitesimalStages
