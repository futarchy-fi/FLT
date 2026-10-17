/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteOriginalCyclicHom
public import FLT.Mazur.PolygonCompleteMarkingAmple
public import FLT.Mazur.RelativeAmpleSectionComparison

/-!
# The ample cyclic subgroup of the complete generalized curve

The faithful original marking constructs a finite subgroup of the full smooth
group. Its scheme-theoretic ideal is exactly the complete product divisor,
whose existing Cartier and ampleness proofs apply across the boundary.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K n h
local notation "φ" => completeOriginalCyclicPointHom K n h
local notation "hφ" => completeOriginalCyclicPointHom_distinct K n h

/-- The original full smooth group contains the finite subgroup of all original cyclic labels. -/
def completeOriginalFiniteSubgroup : (E).FiniteSubgroup n :=
  (E).relativeCyclicSubgroup (φ) (hφ)

/-- The original label one is a section of the actual finite subgroup. -/
def completeOriginalGenerator : 𝟙_ (Over S) ⟶ (completeOriginalFiniteSubgroup K n h).carrier :=
  (E).relativeCyclicGenerator (φ) (hφ)

/-- Every generator power retains its exact original whole-curve section. -/
theorem completeOriginalGenerator_orbit (i : Fin n) :
    ((completeOriginalGenerator K n h ^ i.val) ≫
      (completeOriginalFiniteSubgroup K n h).curveMap).left = completeBaseMarking K n h i := by
  change ((ConstantCyclicGroup.component S n 1 ^ i.val) ≫
    ConstantCyclicSectionMap.toScheme (φ) ≫ (E).inclusion).left = _
  rw [← ConstantCyclicGenerator.component_pow, ConstantCyclicSectionMap.component_toScheme_assoc,
    completeOriginalCyclicPointHom_curve]
  exact congrArg (completeBaseMarking K n h) ((ZMod.finEquiv n).symm_apply_apply i)

/-- The subgroup's intrinsic closed ideal is the original complete product ideal. -/
theorem completeOriginalFiniteSubgroup_ideal :
    (completeOriginalFiniteSubgroup K n h).ideal = completeMarkingDivisor K n h := by
  rw [completeOriginalFiniteSubgroup, GeneralizedEllipticCurve.relativeCyclicSubgroup_ideal]
  change (∏ i : Fin n, ((completeOriginalGenerator K n h ^ i.val) ≫
    (completeOriginalFiniteSubgroup K n h).curveMap).left.ker) = _
  simp only [completeOriginalGenerator_orbit, completeMarkingDivisor]

/-- The original generator presents the whole relative Cartier subgroup divisor. -/
theorem completeOriginalGenerator_isCartierGenerator :
    (completeOriginalFiniteSubgroup K n h).IsCartierGenerator
      (completeOriginalGenerator K n h) := by
  refine ⟨?_, ?_, ?_⟩
  · change ConstantCyclicGroup.component S n 1 ^ n = 1
    rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
      ConstantCyclicGenerator.component_zero]
  · rw [completeOriginalFiniteSubgroup_ideal]
    exact completeMarkingDivisor_relativeCartier K n h
  · simp only [completeOriginalFiniteSubgroup_ideal, completeOriginalGenerator_orbit,
      completeMarkingDivisor]

/-- The full original subgroup is fppf cyclic, also on the singular closed fiber. -/
theorem completeOriginalFiniteSubgroup_isCyclic :
    (completeOriginalFiniteSubgroup K n h).IsCyclic :=
  (completeOriginalGenerator_isCartierGenerator K n h).isCyclic _

/-- The complete original subgroup is ample on the entire generalized elliptic family. -/
theorem completeOriginalFiniteSubgroup_isAmple :
    (completeOriginalFiniteSubgroup K n h).IsAmple := by
  let _ := exactVeroneseProjToBase_isProper K n h
  unfold FiniteSubgroup.IsAmple
  rw [completeOriginalFiniteSubgroup_ideal]
  exact ⟨(completeMarkingDivisor_relativeCartier K n h).1,
    (completeMarkingLine_relativelyAmple K n h).relativeAmple⟩

end FLT.Mazur.PolygonInfinitesimalStages
