/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingQuadraticModel
public import FLT.Mazur.PolygonSmoothingSpecialFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Flatness of the arithmetic smoothing charts

The original quotient xy = t is isomorphic to its monic quadratic model over
the sum-coordinate line. It is therefore free, and hence flat, over R.
No field, reducedness, or nonzero-parameter hypothesis is required.
-/

@[expose] public noncomputable section

open Polynomial AlgebraicGeometry

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- The quadratic comparison followed by its inverse fixes the original chart. -/
theorem quadraticToChart_comp (t : R) :
    (quadraticToChart t).comp (chartToQuadratic t) = AlgHom.id R _ := by
  apply chartRing_hom_ext t <;> simp

/-- The inverse comparison fixes both the sum variable and the quadratic root. -/
theorem chartToQuadratic_comp (t : R) :
    (chartToQuadratic t).comp (quadraticToChart t) = AlgHom.id R _ := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change chartToQuadratic t (quadraticToChart t (sumCoordinate t)) = sumCoordinate t
    rw [quadraticToChart_sum, map_add, chartToQuadratic_left, chartToQuadratic_right]
    exact sub_add_cancel _ _
  · change chartToQuadratic t (quadraticToChart t (quadraticRoot t)) = quadraticRoot t
    rw [quadraticToChart_root, chartToQuadratic_right]

/-- The original smoothing quotient and the monic quadratic algebra are isomorphic over R. -/
def quadraticEquiv (t : R) : ChartRing t ≃ₐ[R] QuadraticModel t :=
  AlgEquiv.ofAlgHom (chartToQuadratic t) (quadraticToChart t)
    (chartToQuadratic_comp t) (quadraticToChart_comp t)

instance quadraticModel_free_over_line (t : R) : Module.Free R[X] (QuadraticModel t) :=
  (sumQuadratic_monic t).free_adjoinRoot

instance quadraticModel_free (t : R) : Module.Free R (QuadraticModel t) :=
  Module.Free.trans (S := R[X])

instance chartRing_free (t : R) : Module.Free R (ChartRing t) :=
  Module.Free.of_equiv (quadraticEquiv t).symm.toLinearEquiv

instance chartRing_flat (t : R) : Module.Flat R (ChartRing t) := inferInstance

/-- The actual arithmetic structure morphism of the smoothing chart is flat. -/
instance chartStructure_flat (t : R) : Flat (chartStructure R t) := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing t))))
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end FLT.Mazur.PolygonSmoothing
