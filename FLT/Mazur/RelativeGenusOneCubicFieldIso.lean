/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneAffineCartesian
public import FLT.Mazur.RelativeGenusOneNonsingular
public import FLT.Mazur.SmoothCurveCommonOpenBaseChange
public import FLT.Mazur.WeierstrassAffineGeometricIntegral
public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassIntegralProper

/-!
# The original relative cubic morphism on every field test

Base change the retained original affine isomorphism. The affine cubic meets
every field fiber, so it is a common dense open of the two integral curves.
Smoothness of the cubic constructs an inverse to the base-changed original map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (Scheme.Modules.pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅
    structureModule S)

local notation "W" => relativePointWeierstrassCurve G hg s hI e
local notation "q" => G.hom ≫ S.toSpecΓ
local notation "r" => integralCurveStructure (W)
local notation "f" => relativePointToIntegralCubic G hg s hI e

/-- The actual original cubic comparison after an arbitrary coefficient field test. -/
def relativePointCubicFieldMap {K : Type} [Field K] (b : Spec (.of K) ⟶ Spec Γ(S, ⊤)) :
    pullback (q) b ⟶ pullback (r) b :=
  pullback.map _ _ _ _ (f) (𝟙 _) (𝟙 _)
    (by simpa using (relativePointToIntegralCubic_over G hg s hI e).symm) (by simp)

/-- Every field test identifies the entire original curve with its entire cubic. -/
theorem relativePointCubicFieldMap_isIso {K : Type} [Field K]
    (b : Spec (.of K) ⟶ Spec Γ(S, ⊤)) : IsIso (relativePointCubicFieldMap G hg s hI e b) := by
  let U := (s.left.ker.support.compl : G.left.Opens)
  let E := relativePointIntegralAffineIso G hg s hI e
  let j := E.inv ≫ Scheme.Opens.ι (X := G.left) U
  let k := integralCurveChart (W) 2
  have hjk : j ≫ (f) = k := by
    dsimp only [j, E, k, U]
    rw [Category.assoc, ← relativePointIntegralAffineIso_chart, Iso.inv_hom_id_assoc]
  let _ : GeometricallyIntegral (q) :=
    (MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral G.hom
      S.toSpecΓ).mpr inferInstance
  let _ := relativePointWeierstrass_projective_smooth_dimension G hg s hI e
  have hu : IsIntegral (pullback (k ≫ (r)) b) := by
    change IsIntegral (pullback (integralCurveChart (W) 2 ≫ (r)) b)
    rw [integralCurveChart_structure]
    exact GeometricallyIntegral.geometrically_isIntegral b _ _ (.of_hasPullback _ _)
  let _ := hu
  exact smoothCurve_commonOpen_fieldBaseChange_isIso (q) (r) j k (f)
    (relativePointToIntegralCubic_over G hg s hI e) hjk b

/-- The fiber isomorphism retains the original global cubic map under projection. -/
@[reassoc] theorem relativePointCubicFieldMap_fst {K : Type} [Field K]
    (b : Spec (.of K) ⟶ Spec Γ(S, ⊤)) :
    relativePointCubicFieldMap G hg s hI e b ≫ pullback.fst (r) b =
      pullback.fst (q) b ≫ (f) := by
  simp [relativePointCubicFieldMap]

end FLT.Mazur.FCurve
