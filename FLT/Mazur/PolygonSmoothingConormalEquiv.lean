/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingConormalMap

/-!
# The original arithmetic conormal module is free of rank one

Over a domain the original equation is nonzero, so its principal ideal is
free. Tensoring this ideal with the chart identifies I/I² with the chart ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

open TensorProduct

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (t : R)

/-- The original equation is nonzero over every nontrivial coefficient ring. -/
theorem relation_ne_zero [Nontrivial R] : relation t ≠ 0 := by
  intro h
  have hd := congrArg (fun f : MvPolynomial (Fin 2) R ↦
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 f)) h
  simp [relation] at hd

variable [IsDomain R]

/-- Multiplication by the original equation identifies its kernel ideal with a free module. -/
def chartRelationIdealEquiv : MvPolynomial (Fin 2) R ≃ₗ[MvPolynomial (Fin 2) R]
    (chartGenerators t).ker :=
  (LinearEquiv.toSpanNonzeroSingleton _ _ (relation t) (relation_ne_zero t)) ≪≫ₗ
    LinearEquiv.ofEq _ _ (chartGenerators_ker t).symm

/-- The original conormal module has basis the class of xy-t. -/
def chartConormalEquiv : ChartRing t ≃ₗ[ChartRing t]
    (chartGenerators t).toExtension.Cotangent :=
  (AlgebraTensorModule.rid (MvPolynomial (Fin 2) R) (ChartRing t) (ChartRing t)).symm ≪≫ₗ
    (chartRelationIdealEquiv t).baseChange (MvPolynomial (Fin 2) R) (ChartRing t)
      (MvPolynomial (Fin 2) R) ((chartGenerators t).ker) ≪≫ₗ
      (chartGenerators t).toExtension.cotangentEquiv

/-- The free conormal generator is the class of the original equation. -/
theorem chartConormalEquiv_apply (a : ChartRing t) :
    chartConormalEquiv t a = a • conormalRelation t := by
  change (chartGenerators t).toExtension.cotangentEquiv
    (a ⊗ₜ[MvPolynomial (Fin 2) R] chartRelationIdealEquiv t 1) = _
  change a • Algebra.Extension.Cotangent.mk
    (P := (chartGenerators t).toExtension) (chartRelationIdealEquiv t 1) = _
  congr 1
  congr 1
  apply Subtype.ext
  change (1 : MvPolynomial (Fin 2) R) • relation t = relation t
  exact one_smul _ _

attribute [local irreducible] chartConormalEquiv

/-- In the constructed conormal basis the actual differential is the original relation map. -/
theorem chartConormalMap_comp_equiv :
    (chartConormalMap t).comp (chartConormalEquiv t).toLinearMap =
      TwoGeneratorRelation.relationMap (leftCoordinate t) (rightCoordinate t) := by
  apply LinearMap.ext
  intro a
  exact (congrArg (chartConormalMap t) (chartConormalEquiv_apply t a)).trans
    (chartConormalMap_smul_relation t a)

end FLT.Mazur.PolygonSmoothing
