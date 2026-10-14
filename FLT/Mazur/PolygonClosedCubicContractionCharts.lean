/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointIdentityBaseChange
public import FLT.Mazur.PolygonCompleteClosedPointLineComparison
public import FLT.Mazur.PolygonOneGonContractionMarking
public import FLT.Mazur.CommonUnchangedOpenComparison
public import FLT.Mazur.SchemeUnchangedOpen

/-!
# Common identity charts for the closed cubic and the actual polygon contraction

On the original closed polygon, intersect the unchanged cubic neighborhood
with the retained Laurent component of the explicit one-gon contraction.
This common source contains the unchanged unit-one marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointIdentityCubicOpen

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "P" => PolygonCyclicAtlas.scheme K n h
local notation "U" => completePointIdentityBaseChangeOpen K n h (completeClosedBase K) i
local notation "V" => Scheme.Hom.opensRange (Over.Hom.left (PolygonAtlas.torus K 1 0))

/-- The actual complete-base cubic map restricted to the original closed polygon. -/
def closedPointToCubic : P ⟶ completePointCubicBaseChange K n h (completeClosedBase K) i :=
  completePointToCubicBaseChange K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h) i

/-- The actual contraction of the same original polygon onto its selected one-gon. -/
def closedPointContraction : P ⟶ (PolygonAtlas.polygon K 1).left :=
  (contraction K n (by omega) (PolygonCyclicAtlas.normalization K n h)
    (PolygonCyclicAtlas.nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega)) i).left

/-- The closed cubic comparison is unchanged over the original identity neighborhood. -/
theorem closedPointToCubic_identity_isIso : IsIso ((closedPointToCubic K n h i) ∣_ (U)) :=
  completePointIdentityBaseChangeOpen_isIso K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h) i

/-- The actual contraction is unchanged over the target Laurent component. -/
theorem closedPointContraction_torus_isIso : IsIso ((closedPointContraction K n h i) ∣_ (V)) :=
  SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
    (contraction_torus_square K n (by omega) (PolygonCyclicAtlas.normalization K n h)
      (PolygonCyclicAtlas.nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega)) i)

/-- The original unit-one marking with its specified closed-fiber scheme as codomain. -/
def closedPointMarking : Spec (.of K) ⟶ P :=
  PolygonMarkedSections.sectionMap K n (PolygonCyclicAtlas.normalization K n h) 1 i

/-- The unit-one marking is the original marking on the specified Cartesian closed fiber. -/
theorem closedPointMarking_eq_cartesian :
    closedPointMarking K n h i = completeCartesianMarking K n h (completeClosedBase K)
      (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
      (completeClosedFiber_isPullback K n h) i :=
  (completeCartesianMarking_closed K n h i).symm

/-- The common unchanged open on the original closed polygon. -/
def closedPointCommonIdentityOpen : (P).Opens :=
  CommonUnchangedOpenComparison.sourceOpen
    (closedPointToCubic K n h i) (closedPointContraction K n h i) (U) (V)

/-- The common source contains the entire original unit-one marking. -/
theorem closedPointCommonIdentityOpen_marking_range :
    Set.range (closedPointMarking K n h i) ⊆ closedPointCommonIdentityOpen K n h i := by
  rintro _ ⟨x, rfl⟩
  constructor
  · have hm := completePointIdentityBaseChangeOpen_marking_range K n h (completeClosedBase K)
      (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
      (completeClosedFiber_isPullback K n h) i
    rw [closedPointMarking_eq_cartesian]
    exact hm ⟨x, rfl⟩
  · change (closedPointMarking K n h i ≫ closedPointContraction K n h i) x
        ∈ Set.range (PolygonAtlas.torus K 1 0).left
    rw [closedPointMarking, closedPointContraction, section_contraction]
    exact PolygonMarkedSections.section_mem_torus K 1 (PolygonAtlas.normalization K 1) 1 0 x

end FLT.Mazur.PolygonInfinitesimalStages
