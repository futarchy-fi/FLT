/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseFiniteType
public import FLT.Mazur.PolygonVeroneseZeroRing
public import FLT.Mazur.GradedProjStructuralMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Proper Proj of the original compatible Veronese algebra

The actual finite-type algebra and its original degree-zero coefficient
ring define a proper scheme over the power-series base. Comparing its
reductions with the given polygon stages is a separate construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The projective spectrum of the actual compatible Veronese algebra. -/
def exactVeroneseProj : Scheme :=
  Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))

/-- The original complete coefficients define the structural morphism of this Proj. -/
def exactVeroneseProjToBase : exactVeroneseProj K n h ⟶ Spec (.of (PowerSeries K)) :=
  GradedProjStructuralMap.toSpecBase
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))

/-- The actual compatible algebra is also finite type over its internal degree-zero ring. -/
theorem exactVeronese_finiteType_zero : Algebra.FiniteType
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h) 0)
    (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) := by
  let _ := exactVeronese_finiteType K n h
  let _ : IsScalarTower (PowerSeries K)
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h) 0)
      (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) :=
    IsScalarTower.of_algebraMap_eq (R := PowerSeries K)
      (S := compatibleVeroneseGrade K n h (exactVeroneseStep K n h) 0)
      (A := CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) fun _ ↦ rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType (PowerSeries K)
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h) 0)
    (CompatibleVeroneseSections K n h (exactVeroneseStep K n h))

/-- The original compatible section algebra defines a proper scheme over the complete base. -/
theorem exactVeroneseProjToBase_isProper : IsProper (exactVeroneseProjToBase K n h) := by
  let _ := exactVeronese_finiteType_zero K n h
  let e := (compatibleVeroneseZeroRingEquiv K n h (exactVeroneseStep K n h)).toCommRingCatIso
  change IsProper (Proj.toSpecZero
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) ≫ Spec.map e.hom)
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
