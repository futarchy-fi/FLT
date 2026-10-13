/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartNoetherian
public import FLT.Mazur.HilbertAmbientClosedParameter
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite type of the actual finite-coordinate Hilbert parameters

The original structure-constant rings are quotients of finite polynomial rings.
Their actual glued structure morphism is locally of finite type, as is its
full closed ambient restriction. No finiteness of the ambient ideal is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
universe u
set_option backward.isDefEq.respectTransparency false
variable (R I : Type u) [CommRing R] [Finite I] (d : ℕ)

/-- Finite coordinates make each original prescribed-basis algebra of finite type. -/
instance chartRing_finiteType (w : Fin d → MvPolynomial I R) :
    Algebra.FiniteType R (ChartRing R I d w) := by
  let _ : CommRing (Coefficients R I d) := inferInstance
  let _ : Algebra.FiniteType R (Parameters R I d) := inferInstance
  let _ : Algebra.FiniteType R (Coefficients R I d) := inferInstance
  infer_instance

/-- The glued polynomial Hilbert scheme retains a locally finite type base morphism. -/
instance polynomialHilbertStructure_locallyOfFiniteType :
    LocallyOfFiniteType (polynomialHilbertStructure R I d) := by
  apply IsZariskiLocalAtSource.of_openCover (polynomialHilbertSchemeCover R I d)
  intro w
  change LocallyOfFiniteType
    (polynomialHilbertChartι R I d w ≫ polynomialHilbertStructure R I d)
  rw [polynomialHilbertChartι_over]
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- Keeping every ambient relation still gives a locally finite type structure morphism. -/
instance ambientHilbertStructure_locallyOfFiniteType (K : Ideal (MvPolynomial I R)) :
    LocallyOfFiniteType (ambientHilbertStructure R I d K) := by
  unfold ambientHilbertStructure
  infer_instance

end FLT.Mazur.HilbertChart
