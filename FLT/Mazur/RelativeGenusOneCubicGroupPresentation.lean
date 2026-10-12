/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOnePointedPresentation
public import FLT.Mazur.ProperRelativePointedGroupHom
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# The original relative pointed cubic isomorphism preserves the existing group law

Pull back the established Weierstrass group along the original affine base's
canonical spectrum isomorphism. The original complete cubic comparison lifts
to this actual group and preserves multiplication by relative rigidity.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules MonoidalCategory MonObj
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (Scheme.Modules.pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- The original coefficient cubic pulled back to the actual affine base. -/
def relativePointCubicBaseGroup : Over S :=
  (Over.pullback S.toSpecΓ).obj (integralCurveOver (W))

/-- Use the established cubic law and its monoidal pullback. -/
local instance relativePointCubicBaseGrpObj : GrpObj (relativePointCubicBaseGroup G hg s hI e) := by
  let _ := integralCurveGrpObj (W) (relativePointWeierstrass_isElliptic G hg s hI e).isUnit
  exact Functor.grpObjObj

/-- Lift the original complete coordinate comparison to the original base's cubic group. -/
def relativePointCubicBaseMap : G ⟶ relativePointCubicBaseGroup G hg s hI e :=
  Over.homMk (Limits.pullback.lift (relativePointIntegralCubicIso G hg s hI e).hom G.hom
    (relativePointIntegralCubicIso_over G hg s hI e)) (Limits.pullback.lift_snd _ _ _)

/-- The lift projects to exactly the original complete coordinate isomorphism. -/
@[reassoc] theorem relativePointCubicBaseMap_fst :
    (relativePointCubicBaseMap G hg s hI e).left ≫
      Limits.pullback.fst (integralCurveStructure (W)) S.toSpecΓ =
        (relativePointIntegralCubicIso G hg s hI e).hom :=
  Limits.pullback.lift_fst _ _ _

/-- The actual lifted comparison is still an isomorphism. -/
instance relativePointCubicBaseMap_isIso : IsIso (relativePointCubicBaseMap G hg s hI e) := by
  have : IsIso ((relativePointCubicBaseMap G hg s hI e).left ≫
      Limits.pullback.fst (integralCurveStructure (W)) S.toSpecΓ) := by
    rw [relativePointCubicBaseMap_fst]
    infer_instance
  have : IsIso (relativePointCubicBaseMap G hg s hI e).left :=
    (isIso_comp_right_iff _ (Limits.pullback.fst
      (integralCurveStructure (W)) S.toSpecΓ)).mp inferInstance
  have : IsIso ((Over.forget S).map (relativePointCubicBaseMap G hg s hI e)) := this
  exact isIso_of_reflects_iso _ (Over.forget S)

/-- The specified marking maps to the identity of the existing pulled-back cubic law. -/
theorem relativePointCubicBaseMap_marking :
    s ≫ relativePointCubicBaseMap G hg s hI e = η[relativePointCubicBaseGroup G hg s hI e] := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (Limits.pullback.fst (integralCurveStructure (W)) S.toSpecΓ)).mp
  rw [Over.comp_left, Category.assoc, relativePointCubicBaseMap_fst]
  rw [relativePointIntegralCubicIso_marking]
  symm
  exact GroupSectionBaseChange.section_fst S.toSpecΓ (integralCurveOverZero (W))

/-- At the original identity, the complete coordinate map preserves the original group laws. -/
theorem relativePointCubicBaseMap_isMonHom (hs : s = η[G]) :
    IsMonHom (relativePointCubicBaseMap G hg s hI e) := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_affine_cover
    (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top S⟩) (by simp) (fun _ ↦ inferInstance)
  let _ : IsSeparated (relativePointCubicBaseGroup G hg s hI e).hom :=
    inferInstanceAs (IsSeparated (Limits.pullback.snd (integralCurveStructure (W)) S.toSpecΓ))
  let _ : LocallyOfFiniteType (relativePointCubicBaseGroup G hg s hI e).hom :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.snd (integralCurveStructure (W)) S.toSpecΓ))
  apply properRelative_isMonHom_of_one G (relativePointCubicBaseGroup G hg s hI e)
  rw [← hs]
  exact relativePointCubicBaseMap_marking G hg s hI e

end FLT.Mazur.FCurve
