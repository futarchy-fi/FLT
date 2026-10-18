/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteGeneralizedCurve
public import FLT.Mazur.OneGonSmoothingCyclicCartier
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# Actual generalized-curve subgroups from faithful complete cyclic parameters

Every scheme test of the faithful parameter space gives a finite subgroup of
the pulled-back complete generalized curve. The full original subgroup map,
ideal, and Cartier generator are retained, including on singular fibers.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonSmoothing
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
local notation "t" => (PowerSeries.X : PowerSeries K)
variable {T : Scheme} (g : T ⟶ Spec (.of (PowerSeries K)))
  (f : Over.mk g ⟶ relativeCyclicParameter (PowerSeries.X : PowerSeries K) n)

/-- A faithful parameter gives an actual subgroup of the full generalized curve. -/
def completeParameterSubgroup : ((completeGeneralizedCurve K).baseChange g).FiniteSubgroup n where
  carrier := ConstantCyclicGroup.model T n
  inclusion := relativeCyclicInclusion (t) n g f
  degree := ConstantCyclicRelativeGeometry.degree T n

/-- Its whole-curve map is exactly the original faithful-parameter map. -/
theorem completeParameterSubgroup_curveMap :
    (completeParameterSubgroup K n g f).curveMap = relativeCyclicCurveMap (t) n g f := by
  change relativeCyclicInclusion (t) n g f ≫
    ((completeGeneralizedCurve K).baseChange g).inclusion = _
  rw [baseChange_inclusion]
  change relativeCyclicInclusion (t) n g f ≫
    (Over.pullback g).map (completeGeneralizedCurve K).inclusion = _
  rw [completeGeneralizedCurve_inclusion]
  rfl

/-- The intrinsic ideal retains the entire original parameter-dependent cyclic ideal. -/
theorem completeParameterSubgroup_ideal :
    (completeParameterSubgroup K n g f).ideal = relativeCyclicIdeal (t) n g f := by
  unfold FiniteSubgroup.ideal
  rw [completeParameterSubgroup_curveMap]
  rfl

/-- The parameter's original component-one section lies in the actual subgroup. -/
def completeParameterGenerator :
    𝟙_ (Over T) ⟶ (completeParameterSubgroup K n g f).carrier := relativeCyclicGenerator n

/-- The original complete parameter gives a Cartier generator of the whole actual subgroup. -/
theorem completeParameterGenerator_isCartierGenerator :
    (completeParameterSubgroup K n g f).IsCartierGenerator
      (completeParameterGenerator K n g f) := by
  refine ⟨?_, ?_, ?_⟩
  · change ConstantCyclicGroup.component T n 1 ^ n = 1
    rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
      ConstantCyclicGenerator.component_zero]
  · rw [completeParameterSubgroup_ideal]
    exact relativeCyclicIdeal_cartier (t) n g f
  · rw [completeParameterSubgroup_ideal, completeParameterSubgroup_curveMap]
    exact relativeCyclicIdeal_generator_product (t) n g f

/-- Every faithful parameter test defines a cyclic subgroup of the actual generalized curve. -/
theorem completeParameterSubgroup_isCyclic :
    (completeParameterSubgroup K n g f).IsCyclic :=
  (completeParameterGenerator_isCartierGenerator K n g f).isCyclic _

end FLT.Mazur.OneGonSmoothing
