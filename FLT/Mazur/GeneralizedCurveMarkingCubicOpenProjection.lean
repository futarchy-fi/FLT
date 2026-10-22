/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkedCubicComparison
public import FLT.Mazur.GeneralizedCurveMarkingCubicProjection
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Open restrictions of the constructed whole cubic

The projection for independently recomputed coordinates is cartesian over the
coefficient spectrum. In particular an open base restriction gives an actual
open immersion of the whole cubics, including their singular fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback smoothMarkingWeierstrassCurve
variable {S T : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : SmoothMarkingFrame E s)
  (b : SmoothMarkingFrame (E.baseChange g) (pullSection g s))
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "V" => smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b

/-- The independently framed projection is cartesian over the actual coefficient map. -/
theorem smoothMarkingCubicProjection_isPullback :
    IsPullback (smoothMarkingCubicProjection E g s a b) (integralCurveStructure V)
      (integralCurveStructure W) (Spec.map g.appTop) := by
  apply IsPullback.of_iso_pullback ⟨smoothMarkingCubicProjection_over E g s a b⟩
    (smoothMarkingCubicPullbackIso E g s a b)
  · rfl
  · exact smoothMarkingCubicPullbackIso_snd E g s a b

/-- An open restriction on the base is an open restriction of the entire cubic. -/
theorem smoothMarkingCubicProjection_isOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (smoothMarkingCubicProjection E g s a b) := by
  have hg : Spec.map g.appTop = T.isoSpec.inv ≫ g ≫ S.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  let _ : IsOpenImmersion (Spec.map g.appTop) := by
    rw [hg]
    infer_instance
  unfold smoothMarkingCubicProjection
  infer_instance

/-- The image of the full cubic restriction is precisely the inverse image of the base image. -/
theorem smoothMarkingCubicProjection_range :
    Set.range (smoothMarkingCubicProjection E g s a b) =
      integralCurveStructure W ⁻¹' Set.range (Spec.map g.appTop) := by
  simp only [smoothMarkingCubicProjection, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr (smoothMarkingCubicPullbackIso E g s a b).hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
