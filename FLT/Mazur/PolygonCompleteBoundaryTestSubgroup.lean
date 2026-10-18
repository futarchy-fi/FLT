/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTestFaithful
public import FLT.Mazur.PolygonCompleteBoundaryTestDivisor
public import FLT.Mazur.PolygonCompleteBoundarySubgroupCurve
public import FLT.Mazur.PolygonBoundaryCyclicSubgroup

/-!
# Actual boundary parameters recover the original complete-family subgroup

The subgroup constructed from the actual faithful boundary parameter has the
original complete product ideal. Its compatible isomorphism retains the full
complete-family curve, group law and subgroup embedding over the original test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonUniversalAction CyclicBoundaryParameter GeneralizedEllipticCurve
open GeneralizedEllipticCurve.FiniteSubgroup PolygonCyclicBoundary
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ G K n))
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "E" => PolygonGeneralizedCurve.curve K n hn p q hp
local notation "f" => completeBoundaryTestParameter K n h g a b
local notation "hf" => completeBoundaryTestParameter_distinct K n h g a b
local notation "J" => FiniteSubgroup.baseChange (completeClosedFiniteSubgroup K n h) g

/-- The actual subgroup built from the complete family's original boundary parameter. -/
def completeBoundaryTestSubgroup : ((E).baseChange g).FiniteSubgroup n :=
  parameterSubgroup K n hn p q hp n g (f) (hf)

/-- The actual parameter subgroup has exactly the original product of its cyclic labels. -/
theorem completeBoundaryTestSubgroup_ideal :
    (completeBoundaryTestSubgroup K n h g a b).ideal =
      completeBoundaryTestIdeal K n h g a b := by
  rw [completeBoundaryTestSubgroup, parameterSubgroup, relativeCyclicSubgroup_ideal]
  unfold completeBoundaryTestIdeal
  apply Finset.prod_congr rfl
  intro i _
  change ((ConstantCyclicGroup.component T n 1 ^ i.val) ≫
    ConstantCyclicSectionMap.toScheme (cyclicSectionMarking (G K n) n g (f)) ≫
      ((E).baseChange g).inclusion).left.ker = _
  rw [← ConstantCyclicGenerator.component_natCast,
    ConstantCyclicSectionMap.component_toScheme_assoc, cyclicSectionMarking_apply]

/-- The parameter retains the actual original subgroup over its whole boundary curve. -/
def completeBoundaryTestClosedIso :
    CompatibleIso (completeBoundaryTestSubgroup K n h g a b) (J) :=
  compatibleIsoOfIdealEq _ _ ((completeBoundaryTestSubgroup_ideal K n h g a b).trans
    (completeBoundaryTestIdeal_eq K n h g a b))

/-- The actual boundary test recovers the full original complete-family subgroup data. -/
def completeBoundaryTestOriginalIso :
    CompatibleIso (completeBoundaryTestSubgroup K n h g a b)
      ((completeOriginalFiniteSubgroup K n h).baseChange (g ≫ completeClosedBase K)) :=
  (completeBoundaryTestClosedIso K n h g a b).trans
    (completeBoundarySubgroupIso K n h g).symm

/-- The recovered complete curve uses the unchanged original Cartesian boundary comparison. -/
theorem completeBoundaryTestOriginalIso_curve :
    (completeBoundaryTestOriginalIso K n h g a b).curve =
      (completeBoundarySubgroupIso K n h g).curve.symm := by
  change Iso.refl _ ≪≫ (completeBoundarySubgroupIso K n h g).curve.symm = _
  exact Iso.refl_trans _

/-- The actual constructed parameter subgroup retains the original full divisor's ampleness. -/
theorem completeBoundaryTestSubgroup_isAmple :
    (completeBoundaryTestSubgroup K n h g a b).IsAmple := by
  unfold FiniteSubgroup.IsAmple
  rw [completeBoundaryTestSubgroup_ideal]
  exact ⟨(completeBoundaryTestIdeal_cartier K n h g a b).1,
    completeBoundaryTestIdeal_ample K n h g a b⟩

end FLT.Mazur.PolygonInfinitesimalStages
