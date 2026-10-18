/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedSubgroupIso
public import FLT.Mazur.CompatibleSubgroupIsoBaseChange
public import FLT.Mazur.GeneralizedCurveAmpleBaseChange
public import FLT.Mazur.PolygonCompleteBoundaryParameter

/-!
# The original complete subgroup over arbitrary boundary tests

The full complete-family subgroup specializes over every scheme over the closed
field. Its comparison with the original polygon subgroup preserves the whole
curve and the subgroup embedding, including the original product ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "b" => completeClosedBase K
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h

/-- Arbitrary boundary tests retain the actual complete subgroup and its full curve. -/
def completeBoundarySubgroupIso :
    CompatibleIso ((H).baseChange (g ≫ b)) ((J).baseChange g) :=
  (compatibleBaseChangeComp H b g).trans ((completeClosedSubgroupIso K n h).baseChange g)

/-- The boundary subgroup has exactly the original complete product ideal pulled back. -/
theorem completeBoundarySubgroup_ideal :
    ((J).baseChange g).ideal =
      (completeMarkingDivisor K n h).comap (completeBoundaryParameterMap K n h g) := by
  rw [baseChange_ideal, completeClosedFiniteSubgroup_ideal,
    ← Scheme.IdealSheafData.comap_comp]
  rfl

/-- The retained subgroup ideal is the whole original product on the parameter polygon. -/
theorem completeBoundarySubgroup_product :
    ((J).baseChange g).ideal =
      PolygonParameterTranslation.productMarkingIdeal K n p g (fun _ ↦ 1) := by
  rw [completeBoundarySubgroup_ideal, completeMarkingDivisor_boundaryParameter]

/-- The original boundary subgroup remains cyclic over every parameter scheme. -/
theorem completeBoundarySubgroup_isCyclic : ((J).baseChange g).IsCyclic :=
  (completeClosedFiniteSubgroup_isCyclic K n h).baseChange J g

/-- The full original boundary subgroup retains its ampleness under arbitrary base change. -/
theorem completeBoundarySubgroup_isAmple : ((J).baseChange g).IsAmple :=
  (completeClosedFiniteSubgroup_isAmple K n h).baseChange g

end FLT.Mazur.PolygonInfinitesimalStages
