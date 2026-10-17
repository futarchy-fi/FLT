/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveEquivariantIso
public import FLT.Mazur.PolygonCompleteClosedActionComparison
public import FLT.Mazur.PolygonCompleteGeneralizedCurve
public import FLT.Mazur.PolygonGeneralizedCurve

/-!
# The original closed polygon as the full DR fiber

The actual closed curve and split-group comparisons preserve the smooth inclusion.
Together with the whole-action comparison this identifies the full generalized
elliptic curve, including its group law and action at the nodes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeClosedPolygon_lfp exactVeroneseProjToBase_lfp
  completeSmoothGrpObj PolygonPinching.cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "E" => PolygonGeneralizedCurve.curve K n hn P Q hp
local notation "F" => completeGeneralizedCurve K n h
local notation "b" => completeClosedBase K

/-- The actual closed comparisons preserve the original smooth-open inclusion. -/
theorem completeClosedPullback_inclusion :
    (E).inclusion ≫ (completeClosedWholePullbackIso K n h).hom =
      (completeClosedGroupPullbackIso K n h).hom ≫ ((F).baseChange b).inclusion := by
  rw [baseChange_inclusion]
  change (E).inclusion ≫ (completeClosedWholePullbackIso K n h).hom =
    (completeClosedGroupPullbackIso K n h).hom ≫ (Over.pullback b).map (F).inclusion
  rw [completeGeneralizedCurve_inclusion]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, completeClosedWholePullbackIso_fst,
      Over.pullback_map_left]
    erw [pullback.lift_fst]
    rw [← Category.assoc, completeClosedGroupPullbackIso_fst]
    change (PolygonPinching.smoothIso K n hn P Q hp).inv.left ≫
      (PolygonCyclicAtlas.toBase K n h).smoothLocus.ι ≫
        completeClosedFiberInclusion K n h =
      ((PolygonPinching.smoothIso K n hn P Q hp).inv.left ≫
        completeClosedSmoothInclusion K n h) ≫
          (exactVeroneseProjToBase K n h).smoothLocus.ι
    rw [Category.assoc, completeClosedSmoothInclusion_inclusion]
  · exact ((E).inclusion ≫ (completeClosedWholePullbackIso K n h).hom).w.trans
      ((completeClosedGroupPullbackIso K n h).hom ≫
        (Over.pullback b).map (completeWholeSmoothInclusion K n h)).w.symm

/-- The closed smooth-group comparison preserves its full group structure. -/
theorem completeClosedGroupPullbackIso_isMonHom :
    IsMonHom (completeClosedGroupPullbackIso K n h).hom :=
  @isMonHom_of_equivariant _ (E) ((F).baseChange b)
    (completeClosedWholePullbackIso K n h).hom (completeClosedGroupPullbackIso K n h).hom
    (completeClosedPullback_inclusion K n h) (completeClosedPullback_action K n h)

/-- The original closed polygon is the actual full generalized-elliptic-curve fiber. -/
def completeClosedCurveIso : (E) ≅ (F).baseChange b :=
  equivariantIso (completeClosedWholePullbackIso K n h) (completeClosedGroupPullbackIso K n h)
    (completeClosedPullback_inclusion K n h) (completeClosedPullback_action K n h)

/-- The full DR isomorphism retains the original closed-family map. -/
@[reassoc] theorem completeClosedCurveIso_fst :
    (completeClosedCurveIso K n h).hom.curve.left ≫
      pullback.fst (F).curve.hom b = completeClosedFiberInclusion K n h :=
  completeClosedWholePullbackIso_fst K n h

end FLT.Mazur.PolygonInfinitesimalStages
