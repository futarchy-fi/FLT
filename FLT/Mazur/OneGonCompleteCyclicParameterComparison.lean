/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFaithfulCompleteDivisor

/-!
# The lifted subgroup agrees with the original cyclic-parameter construction

Specializing the relative cyclic construction to the completed parameter
over the identity base map gives exactly the subgroup on the original cubic.
This retains the parameter-based construction as a full scheme-map equality.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
local notation "t" => (PowerSeries.X : PowerSeries K)

/-- The canonical identity-base-change projection to the original complete cubic. -/
def completeIdentityCurveProjection : (Over.pullback (𝟙 _)).obj (family (t)) ⟶ family (t) :=
  Over.homMk (pullback.fst (family (t)).hom (𝟙 _))
    (by change _ = pullback.snd _ _
        rw [pullback.condition, Category.comp_id])

/-- The completed parameter's whole-curve map is the constructed original cyclic subgroup. -/
theorem faithfulCompleteCurveMap_parameter :
    relativeCyclicCurveMap (t) n (𝟙 _) (faithfulCompleteParameter K n labels hlabels) ≫
      completeIdentityCurveProjection K = faithfulCompleteCurveMap K n labels hlabels := by
  apply Sigma.hom_ext
  intro i
  change ConstantCyclicGroup.component _ n i ≫ (_ ≫ _) = _
  rw [← Category.assoc, relativeCyclicCurveMap_component, faithfulCompleteCurveMap_component]
  apply Over.OverMorphism.ext
  change (_ ≫ pullback.lift _ _ _) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, faithfulCompleteSections_fst]
  rfl

/-- The canonical projection is an isomorphism of the original underlying curves. -/
instance completeIdentityCurveProjection_isIso :
    IsIso (completeIdentityCurveProjection K).left :=
  inferInstanceAs (IsIso (pullback.fst (family (t)).hom (𝟙 _)))

end FLT.Mazur.OneGonSmoothing
