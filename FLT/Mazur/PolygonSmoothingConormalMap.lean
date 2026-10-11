/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing
public import FLT.Mazur.TwoGeneratorRelationSequence
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# The original arithmetic conormal map in coordinates

The polynomial presentation of xy=t has its genuine conormal module I/I².
Its relation generator maps to (y,x) in the canonical free cotangent space.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (t : R)

/-- The original two polynomial generators of the arithmetic chart. -/
def chartGenerators : Algebra.Generators R (ChartRing t) (Fin 2) :=
  Algebra.Generators.naive

/-- The polynomial kernel is precisely the original equation ideal. -/
theorem chartGenerators_ker : (chartGenerators t).ker = relationIdeal t :=
  Ideal.mk_ker

/-- The class of the original equation in the conormal module. -/
def conormalRelation : (chartGenerators t).toExtension.Cotangent :=
  Algebra.Extension.Cotangent.mk ⟨relation t, by
    change relation t ∈ (chartGenerators t).ker
    rw [chartGenerators_ker]
    exact Ideal.subset_span (Set.mem_singleton _)⟩

/-- The original free cotangent space in the ordered coordinates dx,dy. -/
def chartCotangentSpaceEquiv : (chartGenerators t).toExtension.CotangentSpace ≃ₗ[
    ChartRing t] ChartRing t × ChartRing t :=
  (chartGenerators t).cotangentSpaceBasis.repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite (ChartRing t) (ChartRing t) (Fin 2) ≪≫ₗ
      LinearEquiv.finTwoArrow (ChartRing t) (ChartRing t)

/-- The actual original conormal differential written as a pair. -/
def chartConormalMap : (chartGenerators t).toExtension.Cotangent →ₗ[
    ChartRing t] ChartRing t × ChartRing t :=
  (chartCotangentSpaceEquiv t).toLinearMap.comp
    (chartGenerators t).toExtension.cotangentComplex

/-- Differentiating the original equation gives the ordered pair (y,x). -/
theorem chartConormalMap_relation :
    chartConormalMap t (conormalRelation t) = (rightCoordinate t, leftCoordinate t) := by
  change ((chartGenerators t).cotangentSpaceBasis.repr
    ((chartGenerators t).toExtension.cotangentComplex (conormalRelation t)) 0,
    (chartGenerators t).cotangentSpaceBasis.repr
    ((chartGenerators t).toExtension.cotangentComplex (conormalRelation t)) 1) = _
  simp only [conormalRelation, Algebra.Extension.cotangentComplex_mk,
    Algebra.Generators.cotangentSpaceBasis_repr_one_tmul]
  simp [relation, chartGenerators,
    Algebra.Generators.naive_val, leftCoordinate, rightCoordinate]

/-- Scalar multiples of the equation give the explicit original relation matrix. -/
theorem chartConormalMap_smul_relation (a : ChartRing t) :
    chartConormalMap t (a • conormalRelation t) =
      TwoGeneratorRelation.relationMap (leftCoordinate t) (rightCoordinate t) a := by
  rw [map_smul, chartConormalMap_relation]
  rfl

end FLT.Mazur.PolygonSmoothing
