/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryOriginalAmpleLift
public import FLT.Mazur.PolygonCompleteBoundaryTestSubgroup
public import FLT.Mazur.PolygonBoundaryAmpleParameter
public import FLT.Mazur.CompleteBoundaryAmpleCyclicLevels

/-!
# Complete polygon boundary tests lift to the faithful ample parameter

All original auxiliary labels survive. The pulled-back universal level retains
the original complete family through the existing full-curve/subgroup comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonUniversalAction CyclicBoundaryParameter GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
  (a : UniversalWeierstrass.Labels 4 →* (Over.mk g ⟶ G K n))
  (b : UniversalWeierstrass.Labels 3 →* (Over.mk g ⟶ G K n))
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => Nat.lt_of_lt_of_le (Nat.succ_pos 1) h
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "E" => PolygonGeneralizedCurve.curve K n hn p q hp
local notation "f" => completeBoundaryTestParameter K n h g a b
local notation "hf" => completeBoundaryTestParameter_distinct K n h g a b
local notation "ha" => completeBoundaryTestSubgroup_isAmple K n h g a b

/-- The original complete boundary presentation has a separated smooth group. -/
instance completeAmpleGroup_separated : IsSeparated (E).group.hom :=
  PolygonCyclicBoundary.splitBoundaryGroup_separated K n

/-- The original complete boundary group has relative dimension one. -/
instance completeAmpleGroup_relativeDimension : SmoothOfRelativeDimension 1 (E).group.hom :=
  PolygonCyclicBoundary.splitBoundaryGroup_relativeDimension K n

/-- Every original complete polygon boundary test lifts to its actual ample parameter open. -/
def completeAmpleParameterLift : T ⟶ ampleParameter (E) n :=
  originalAmpleLift (E) n g (f) (hf) (ha)

/-- The lift preserves the original complete parameter and both independent auxiliary markings. -/
@[reassoc] theorem completeAmpleParameterLift_parameter :
    completeAmpleParameterLift K n h g a b ≫ ampleParameterInclusion (E) n = (f).left :=
  originalAmpleLift_parameter (E) n g (f) (hf) (ha)

/-- The actual universal level retains the original complete-family subgroup on this test. -/
def completeAmpleParameterOriginalIso :
    CompatibleIso ((ampleUniversalLevel (E) n).val.2.baseChange
      (completeAmpleParameterLift K n h g a b))
      ((completeOriginalFiniteSubgroup K n h).baseChange (g ≫ completeClosedBase K)) :=
  (originalAmpleLiftSubgroupIso (E) n g (f) (hf) (ha)).symm.trans
    (completeBoundaryTestOriginalIso K n h g a b)

/-- The full curve comparison is the original boundary comparison after the universal lift. -/
theorem completeAmpleParameterOriginalIso_curve :
    (completeAmpleParameterOriginalIso K n h g a b).curve =
      (originalAmpleLiftSubgroupIso (E) n g (f) (hf) (ha)).curve.symm ≪≫
        (completeBoundarySubgroupIso K n h g).curve.symm := by
  change _ ≪≫ (completeBoundaryTestOriginalIso K n h g a b).curve = _
  rw [completeBoundaryTestOriginalIso_curve]
  rfl

/-- The actual modular map at the lift recovers the original complete polygon class. -/
theorem ampleModuliMap_completeAmpleParameterLift :
    (ampleModuliMap (E) n).app (Opposite.op T)
      (ULift.up (completeAmpleParameterLift K n h g a b)) =
        ampleCyclicClassesPullback (g ≫ completeClosedBase K) n
          (Quotient.mk _ (CompleteBoundaryLevels.polygonLevel K n h)) :=
  Quotient.sound ⟨completeAmpleParameterOriginalIso K n h g a b⟩

end FLT.Mazur.PolygonInfinitesimalStages
