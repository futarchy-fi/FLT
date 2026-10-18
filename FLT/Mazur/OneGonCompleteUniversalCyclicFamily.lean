/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingCyclicIdeal
public import FLT.Mazur.OneGonSmoothingGenusOneFamily

/-!
# The actual complete one-gon family over its faithful cyclic parameter scheme

The identity parameter constructs the universal rank-n subgroup and its full
closed embedding. The complete-family geometric contract persists over this
base. This does not assert that every closed one-gon marking lifts to that base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "P" => relativeCyclicParameter (t) n

/-- The original complete family over its actual faithful cyclic-marking parameter scheme. -/
def completeUniversalCyclicFamily : Over (P).left :=
  (Over.pullback (P).hom).obj (family (t))

/-- The universal finite cyclic subgroup retains its original full-curve embedding. -/
def completeUniversalCyclicMap :
    ConstantCyclicGroup.model (P).left n ⟶ completeUniversalCyclicFamily K n :=
  relativeCyclicCurveMap (t) n (P).hom (𝟙 _)

/-- The universal subgroup is closed on the entire complete family over the parameter scheme. -/
theorem completeUniversalCyclicMap_closed :
    IsClosedImmersion (completeUniversalCyclicMap K n).left :=
  relativeCyclicCurveMap_closed (t) n (P).hom (𝟙 _)

/-- The full genus-one family contract survives the actual cyclic parameter change. -/
theorem completeUniversalCyclicFamily_classified :
    FCurve.ClassifiedGenusOneFamily (completeUniversalCyclicFamily K n).hom :=
  completeBaseChange_classifiedGenusOneFamily K (P).hom

/-- The actual universal subgroup is finite locally free of rank n over the parameter scheme. -/
theorem completeUniversalCyclic_degree :
    FCurve.FiniteLocallyFreeDegree (ConstantCyclicGroup.model (P).left n).hom n :=
  ConstantCyclicRelativeGeometry.degree (P).left n

/-- The subgroup remains etale, including over the singular closed-fiber parameter locus. -/
theorem completeUniversalCyclic_etale :
    Etale (ConstantCyclicGroup.model (P).left n).hom :=
  ConstantCyclicRelativeGeometry.etale (P).left n

/-- Its actual closed ideal is the full orbit of the specified component-one generator. -/
theorem completeUniversalCyclicMap_ideal :
    (completeUniversalCyclicMap K n).left.ker = ∏ i : Fin n,
      ((relativeCyclicGenerator (T := (P).left) n ^ i.val) ≫
        completeUniversalCyclicMap K n).left.ker :=
  relativeCyclicIdeal_generator_product (t) n (P).hom (𝟙 _)

end FLT.Mazur.OneGonSmoothing
