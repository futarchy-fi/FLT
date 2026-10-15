/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticFiniteType
public import FLT.Mazur.PolygonArithmeticVeroneseZeroRing
public import FLT.Mazur.GradedProjStructuralMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Proper Proj of the original compatible Veronese algebra

The actual finite-type algebra and its original degree-zero coefficient
ring define a proper scheme over the integral base. Comparing its
reductions with the given polygon stages is a separate construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] [NeZero n]

/-- The projective spectrum of the actual compatible Veronese algebra. -/
def exactVeroneseProj : Scheme :=
  Proj (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))

/-- The original complete coefficients define the structural morphism of this Proj. -/
def exactVeroneseProjToBase : exactVeroneseProj A π n h hne hgen ⟶ Spec (.of A) :=
  GradedProjStructuralMap.toSpecBase
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))

/-- The actual compatible algebra is also finite type over its internal degree-zero ring. -/
theorem exactVeronese_finiteType_zero : Algebra.FiniteType
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) 0)
    (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) := by
  let _ := exactVeronese_finiteType A π hne hgen n h
  let _ : IsScalarTower (A)
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) 0)
      (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) :=
    IsScalarTower.of_algebraMap_eq (R := A)
      (S := compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) 0)
      (A := CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) fun _ ↦ rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType (A)
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) 0)
    (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h))

/-- The original compatible section algebra defines a proper scheme over the complete base. -/
theorem exactVeroneseProjToBase_isProper : IsProper (exactVeroneseProjToBase A π n h hne hgen) := by
  let _ := exactVeronese_finiteType_zero A π n h hne hgen
  let e := (compatibleVeroneseZeroRingEquiv A π n h (exactVeroneseStep A π hne hgen n h) hne
      hgen).toCommRingCatIso
  change IsProper (Proj.toSpecZero
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)) ≫ Spec.map e.hom)
  infer_instance

end FLT.Mazur.PolygonArithmeticStages
