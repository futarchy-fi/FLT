/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonClosedGroupInclusion
public import FLT.Mazur.OneGonOriginalGroupComparison
public import FLT.Mazur.OneGonCompleteGeneralizedCurve
public import FLT.Mazur.PolygonGeneralizedCurveActionExt

/-!
# The original pinched one-gon is the full closed DR fiber

The original whole-curve and corrected smooth-group comparisons preserve the
smooth inclusion. Density of the component tori proves equivariance everywhere,
so this comparison retains the full generalized elliptic curve and its action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OneGonSmoothing
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]
local notation "p" => OneGonNormalization.normalizationOver K
local notation "q" => OneGonNormalization.nodes K
local notation "hp" => OneGonGlobalPushout.isPushout K (by decide)
local notation "E" => PolygonGeneralizedCurve.curve K 1 (by decide) p q hp
local notation "F" => completeGeneralizedCurve K
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The original pinching comparison as an isomorphism of the actual closed relative curves. -/
def completeClosedWholePullbackIso : (E).curve ≅ ((F).baseChange (c)).curve :=
  Over.isoMk (powerSeriesClosedFiberIso K) (powerSeriesClosedFiberIso_snd K)

/-- The corrected original group comparison on the actual closed smooth carrier. -/
def completeClosedOriginalGroupOverIso : (E).group ≅ ((F).baseChange (c)).group :=
  (CommGrp.forget (Over (Spec (.of K)))).mapIso (originalOneGonClosedGroupIso K)

/-- The closed inclusion retains the original complete-family smooth-open embedding. -/
@[reassoc] theorem completeClosedInclusion_fst :
    ((F).baseChange (c)).inclusion.left ≫ pullback.fst (family (t)).hom (c) =
      pullback.fst (relativeGroup (t)).X.hom (c) ≫ (relativeGroupInclusion (t)).left := by
  rw [baseChange_inclusion]
  change ((Over.pullback (c)).map (F).inclusion).left ≫ _ = _
  rw [completeGeneralizedCurve_inclusion]
  exact pullback.lift_fst _ _ _

/-- Forgetting the relative whole-curve comparison gives the original fiber comparison. -/
theorem completeClosedWholePullbackIso_hom_left :
    (completeClosedWholePullbackIso K).hom.left = (powerSeriesClosedFiberIso K).hom := rfl

/-- The original smooth inclusion on each singleton component is the torus open. -/
theorem completeClosedOriginalInclusion_component (i : ZMod 1) :
    (PolygonSplitGroup.component K 1 i).left ≫ (E).inclusion.left = OneGonGluing.torus K :=
  originalOneGon_inclusion_component K i

/-- The corrected group comparison retains its actual scheme map on each component. -/
theorem completeClosedOriginalGroupOverIso_component (i : ZMod 1) :
    (PolygonSplitGroup.component K 1 i).left ≫
      (completeClosedOriginalGroupOverIso K).hom.left =
        ι[MultiplicativeGroupScheme.gm K].left ≫
          (completeClosedGroupTorusOverIso K).inv.left :=
  congrArg Over.Hom.left (originalOneGonClosedGroupIso_component K i)

/-- The actual closed inclusion square on each original smooth component. -/
theorem completeClosedPullback_component (i : ZMod 1) :
    PolygonSplitGroup.component K 1 i ≫ (E).inclusion ≫
      (completeClosedWholePullbackIso K).hom =
    PolygonSplitGroup.component K 1 i ≫ (completeClosedOriginalGroupOverIso K).hom ≫
      ((F).baseChange (c)).inclusion := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, completeClosedWholePullbackIso_hom_left]
    rw [← Category.assoc (PolygonSplitGroup.component K 1 i).left,
      completeClosedOriginalInclusion_component]
    erw [powerSeriesClosedFiberIso_torus_fst K, completeClosedInclusion_fst K]
    rw [← Category.assoc (PolygonSplitGroup.component K 1 i).left,
      completeClosedOriginalGroupOverIso_component]
    exact (Category.assoc _ _ _).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- The actual whole-curve comparison and corrected group comparison preserve the inclusion. -/
theorem completeClosedPullback_inclusion :
    (E).inclusion ≫ (completeClosedWholePullbackIso K).hom =
      (completeClosedOriginalGroupOverIso K).hom ≫ ((F).baseChange (c)).inclusion := by
  apply Sigma.hom_ext
  intro i
  exact completeClosedPullback_component K i

/-- The original closed pinched polygon is the entire generalized elliptic curve fiber. -/
def completeClosedCurveIso : (E) ≅ (F).baseChange (c) := by
  let _ : IsMonHom (completeClosedOriginalGroupOverIso K).hom :=
    (originalOneGonClosedGroupIso K).hom.hom.hom.isMonHom_hom
  exact PolygonGeneralizedCurve.isoOfInclusion K 1 (by decide) (p) (q) (hp)
    (completeClosedWholePullbackIso K) (completeClosedOriginalGroupOverIso K)
    (completeClosedPullback_inclusion K)

/-- The full DR isomorphism retains the original whole-curve comparison. -/
theorem completeClosedCurveIso_curve :
    (completeClosedCurveIso K).hom.curve.left = (powerSeriesClosedFiberIso K).hom := rfl

/-- The full DR isomorphism retains the corrected original smooth-group comparison. -/
theorem completeClosedCurveIso_group :
    (completeClosedCurveIso K).hom.group =
      (originalOneGonClosedGroupIso K).hom.hom.hom.hom := rfl

/-- Equivariance holds on the entire curve, including the pinched node. -/
theorem completeClosedCurveIso_action :
    (E).act ≫ (completeClosedCurveIso K).hom.curve =
      ((completeClosedCurveIso K).hom.group ⊗ₘ (completeClosedCurveIso K).hom.curve) ≫
        ((F).baseChange (c)).act := (completeClosedCurveIso K).hom.action

end FLT.Mazur.OneGonSmoothing
