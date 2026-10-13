/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodeConicBranch
public import FLT.Mazur.WeierstrassModificationXFullNodeIncidenceBranch
public import FLT.Mazur.WeierstrassModificationXFullNodePushout
public import FLT.Mazur.BinaryOpenDescent

/-!
# The complete incidence line and conic detect arbitrary scheme morphisms

Use both actual node pushouts and their open cover of the full fiber. This is
scheme-theoretic uniqueness for arbitrary targets, not pointwise detection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
  {Y : Scheme.{u}} (f g : Spec (.of (FiberCoordinate a c)) ⟶ Y)
  (hL : fiberIncidenceImmersion a c ≫ f = fiberIncidenceImmersion a c ≫ g)
  (hC : fiberConicImmersion a c ≫ f = fiberConicImmersion a c ≫ g)

include ha hL hC in
/-- The entire incidence line and conic detect maps from the original full equation. -/
theorem fullFiber_components_hom_ext : f = g := by
  apply BinaryOpenDescent.hom_ext _ _ (fullNodeCharts_cover a c ha)
  · apply (fullNodeBranches_isPushout a c ha).hom_ext
    · apply (cancel_epi (fullNodeConicParameterIso a c ha).hom).mp
      simp only [fullNodeFirstBranch_firstChart_assoc]
      rw [hC]
    · simp only [fullNodeSecondBranch_firstChart_assoc]
      rw [hL]
  · apply (fullNodeBranches_isPushout (-a) c ha.neg).hom_ext
    · apply (cancel_epi (fullNodeConicParameterIso (-a) c ha.neg).hom).mp
      simp only [fullNodeFirstBranch_secondChart_assoc]
      rw [hC]
    · simp only [fullNodeSecondBranch_secondChart_assoc]
      rw [hL]

end FLT.Mazur.WeierstrassModificationX
