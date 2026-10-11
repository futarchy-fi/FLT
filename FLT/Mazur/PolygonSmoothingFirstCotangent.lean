/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingConormalEquiv

/-!
# First cotangent homology of the original arithmetic chart

The presentation-independent first cotangent homology is the kernel of the
explicit original relation matrix. This uses the conormal basis, not only Ω.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (t : R)

attribute [local irreducible] chartCotangentSpaceEquiv chartConormalEquiv

/-- Coordinate identification of the free cotangent space preserves the actual kernel. -/
theorem chartConormalMap_ker :
    LinearMap.ker (chartConormalMap t) =
      LinearMap.ker (chartGenerators t).toExtension.cotangentComplex := by
  exact LinearMap.ker_comp_of_ker_eq_bot _ (chartCotangentSpaceEquiv t).ker

variable [IsDomain R]

/-- The constructed conormal basis identifies the first homology with the relation kernel. -/
def chartH1CotangentEquiv : Algebra.H1Cotangent R (ChartRing t) ≃ₗ[ChartRing t]
    LinearMap.ker (TwoGeneratorRelation.relationMap (leftCoordinate t) (rightCoordinate t)) :=
  (chartGenerators t).equivH1Cotangent.symm ≪≫ₗ
    LinearEquiv.ofEq _ _ (chartConormalMap_ker t).symm ≪≫ₗ
      ((chartConormalEquiv t).ofSubmodule' (LinearMap.ker (chartConormalMap t))).symm ≪≫ₗ
        LinearEquiv.ofEq _ _ (by
          rw [← LinearMap.ker_comp, chartConormalMap_comp_equiv])

/-- A unit original parameter annihilates actual first cotangent homology. -/
theorem chartH1Cotangent_subsingleton_of_isUnit (ht : IsUnit t) :
    Subsingleton (Algebra.H1Cotangent R (ChartRing t)) := by
  have hk := TwoGeneratorRelation.ker_relationMap_of_isUnit_mul
    (leftCoordinate t) (rightCoordinate t) (by
      rw [coordinate_relation]
      exact ht.map (algebraMap R (ChartRing t)))
  let _ : Subsingleton
      (LinearMap.ker (TwoGeneratorRelation.relationMap (leftCoordinate t) (rightCoordinate t))) :=
    Submodule.subsingleton_iff_eq_bot.mpr hk
  exact (chartH1CotangentEquiv t).subsingleton

end FLT.Mazur.PolygonSmoothing
