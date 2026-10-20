/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryOriginalAmpleLift
public import FLT.Mazur.OneGonCompleteBoundaryTestSubgroup
public import FLT.Mazur.PolygonBoundaryAmpleParameter
public import FLT.Mazur.CompleteBoundaryAmpleCyclicLevels

/-!
# Complete one-gon boundary tests lift to the faithful ample parameter

Faithful original cyclic labels and independent auxiliary markings are retained.
The lifted universal level recovers the entire original complete-family subgroup.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open CyclicBoundaryParameter GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  (labels : Multiplicative (ZMod n) →*
    (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
  (hlabels : Function.Injective labels)
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ PolygonSplitGroup.model K 1))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ PolygonSplitGroup.model K 1))
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "hp" => OneGonGlobalPushout.isPushout K Nat.zero_lt_one
local notation "E" => PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one p q hp
local notation "f" => completeBoundaryTestParameter K n labels hlabels g a b
local notation "hf" => completeBoundaryTestParameter_distinct K n labels hlabels g a b
local notation "ha" => completeBoundaryTestSubgroup_isAmple K n labels hlabels g a b
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The original complete boundary presentation has a separated smooth group. -/
instance completeAmpleGroup_separated : IsSeparated (E).group.hom :=
  PolygonCyclicBoundary.splitBoundaryGroup_separated K 1

/-- The original complete boundary group has relative dimension one. -/
instance completeAmpleGroup_relativeDimension : SmoothOfRelativeDimension 1 (E).group.hom :=
  PolygonCyclicBoundary.splitBoundaryGroup_relativeDimension K 1

/-- The original faithful complete one-gon boundary test lifts to its ample parameter open. -/
def completeAmpleParameterLift : T ⟶ ampleParameter (E) n :=
  originalAmpleLift (E) n g (f) (hf) (ha)

/-- The lift retains the entire original parameter, including both auxiliary markings. -/
@[reassoc] theorem completeAmpleParameterLift_parameter :
    completeAmpleParameterLift K n labels hlabels g a b ≫
      ampleParameterInclusion (E) n = (f).left :=
  originalAmpleLift_parameter (E) n g (f) (hf) (ha)

/-- The lifted universal subgroup compares with the actual original complete-family subgroup. -/
def completeAmpleParameterOriginalIso :
    CompatibleIso ((ampleUniversalLevel (E) n).val.2.baseChange
      (completeAmpleParameterLift K n labels hlabels g a b))
      ((completeFiniteSubgroup K n labels hlabels).baseChange (g ≫ (c))) :=
  (originalAmpleLiftSubgroupIso (E) n g (f) (hf) (ha)).symm.trans
    (completeBoundaryTestOriginalIso K n labels hlabels g a b)

/-- The comparison retains the existing full original complete-fiber comparison. -/
theorem completeAmpleParameterOriginalIso_curve :
    (completeAmpleParameterOriginalIso K n labels hlabels g a b).curve =
      (originalAmpleLiftSubgroupIso (E) n g (f) (hf) (ha)).curve.symm ≪≫
        (completeBoundaryTestOriginalIso K n labels hlabels g a b).curve := rfl

/-- The modular transformation at the lift is the unchanged original complete one-gon class. -/
theorem ampleModuliMap_completeAmpleParameterLift :
    (ampleModuliMap (E) n).app (Opposite.op T)
      (ULift.up (completeAmpleParameterLift K n labels hlabels g a b)) =
        ampleCyclicClassesPullback (g ≫ (c)) n
          (Quotient.mk _ (CompleteBoundaryLevels.oneGonLevel K n labels hlabels)) :=
  Quotient.sound ⟨completeAmpleParameterOriginalIso K n labels hlabels g a b⟩

end FLT.Mazur.OneGonSmoothing
