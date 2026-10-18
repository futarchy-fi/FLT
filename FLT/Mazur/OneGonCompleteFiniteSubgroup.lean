/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteGeneralizedCurve
public import FLT.Mazur.OneGonFaithfulCompleteDivisor
public import FLT.Mazur.GeneralizedCurveCartierGenerator

/-!
# The faithful cyclic subgroup of the original complete generalized one-gon

The already constructed closed inclusion gives a finite locally free subgroup
of the actual generalized curve. Its intrinsic ideal and its generator retain
the entire original complete cyclic divisor.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "E" => completeGeneralizedCurve K

/-- The full faithful lifted subgroup inside the original complete generalized curve. -/
def completeFiniteSubgroup : (E).FiniteSubgroup n where
  carrier := ConstantCyclicGroup.model S n
  inclusion := faithfulCompleteInclusion K n labels hlabels
  degree := faithfulCompleteSubgroup_degree K n

/-- Its whole-curve map is the original lifted cyclic map. -/
theorem completeFiniteSubgroup_curveMap :
    (completeFiniteSubgroup K n labels hlabels).curveMap =
      faithfulCompleteCurveMap K n labels hlabels := by
  change faithfulCompleteInclusion K n labels hlabels ≫ (E).inclusion = _
  rw [completeGeneralizedCurve_inclusion]
  rfl

/-- The intrinsic closed subgroup ideal is exactly the full original divisor ideal. -/
theorem completeFiniteSubgroup_ideal :
    (completeFiniteSubgroup K n labels hlabels).ideal =
      faithfulCompleteIdeal K n labels hlabels := by
  unfold FiniteSubgroup.ideal
  rw [completeFiniteSubgroup_curveMap]
  rfl

/-- The original component-one generator in the actual complete subgroup. -/
def completeFiniteGenerator :
    𝟙_ (Over S) ⟶ (completeFiniteSubgroup K n labels hlabels).carrier :=
  relativeCyclicGenerator n

/-- Powers of the generator retain the original labeled full-curve sections. -/
theorem completeFiniteGenerator_orbit (i : Fin n) :
    (completeFiniteGenerator K n labels hlabels ^ i.val) ≫
        (completeFiniteSubgroup K n labels hlabels).curveMap =
      faithfulCompleteMarking K n labels hlabels (.ofAdd (ZMod.finEquiv n i)) ≫
        relativeGroupInclusion (PowerSeries.X : PowerSeries K) := by
  rw [completeFiniteSubgroup_curveMap]
  change (ConstantCyclicGroup.component S n 1 ^ i.val) ≫ _ = _
  rw [← ConstantCyclicGenerator.component_pow, faithfulCompleteCurveMap_component]

/-- The original generator generates the entire actual relative Cartier subgroup divisor. -/
theorem completeFiniteGenerator_isCartierGenerator :
    (completeFiniteSubgroup K n labels hlabels).IsCartierGenerator
      (completeFiniteGenerator K n labels hlabels) := by
  refine ⟨?_, ?_, ?_⟩
  · change ConstantCyclicGroup.component S n 1 ^ n = 1
    rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
      ConstantCyclicGenerator.component_zero]
  · rw [completeFiniteSubgroup_ideal]
    exact faithfulCompleteIdeal_cartier K n labels hlabels
  · rw [completeFiniteSubgroup_ideal, completeFiniteSubgroup_curveMap]
    exact faithfulCompleteIdeal_generator_product K n labels hlabels

end FLT.Mazur.OneGonSmoothing
