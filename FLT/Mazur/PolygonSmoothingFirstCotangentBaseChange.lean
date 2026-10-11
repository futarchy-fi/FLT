/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingFirstCotangent
public import FLT.Mazur.TwoGeneratorRelationKernelBaseChange
public import FLT.Mazur.PolygonSmoothingCotangentRelationSequence

/-!
# Flat scalar extension of original arithmetic first cotangent homology

Flat scalar extension of the original H1 is the explicit relation kernel
with extended original coordinates. Inverting the original parameter kills it.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

open TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R] (t : R)
  (S : Type*) [CommRing S] [Algebra (ChartRing t) S] [Module.Flat (ChartRing t) S]

attribute [local irreducible] chartH1CotangentEquiv

/-- Flat scalar extension of the actual original first homology is the explicit relation kernel. -/
def chartH1CotangentBaseChangeEquiv : S ⊗[ChartRing t] Algebra.H1Cotangent R (ChartRing t) ≃ₗ[S]
    LinearMap.ker (arithmeticCotangentRelation t S) :=
  (chartH1CotangentEquiv t).baseChange (ChartRing t) S _ _ ≪≫ₗ
    TwoGeneratorRelation.relationKernelBaseChangeEquiv (leftCoordinate t) (rightCoordinate t) S

variable [Algebra R S] [IsScalarTower R (ChartRing t) S]

/-- The original H1 vanishes after flat extension making the original parameter a unit. -/
theorem chartH1CotangentBaseChange_subsingleton (ht : IsUnit (algebraMap R S t)) :
    Subsingleton (S ⊗[ChartRing t] Algebra.H1Cotangent R (ChartRing t)) := by
  let _ : Subsingleton (LinearMap.ker (arithmeticCotangentRelation t S)) :=
    Submodule.subsingleton_iff_eq_bot.mpr (arithmeticCotangentRelation_ker_of_isUnit t S ht)
  exact (chartH1CotangentBaseChangeEquiv t S).subsingleton

/-- Localization at the original parameter kills original arithmetic first cotangent homology. -/
theorem chartH1CotangentBaseChange_away
    [IsLocalization.Away (algebraMap R (ChartRing t) t) S] :
    Subsingleton (S ⊗[ChartRing t] Algebra.H1Cotangent R (ChartRing t)) :=
  chartH1CotangentBaseChange_subsingleton t S (by
    rw [IsScalarTower.algebraMap_apply R (ChartRing t) S]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R (ChartRing t) t))

end FLT.Mazur.PolygonSmoothing
