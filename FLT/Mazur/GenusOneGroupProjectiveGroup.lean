/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupProjectivePoint
public import FLT.Mazur.ProperGroupPointedHom
public import FLT.Mazur.WeierstrassGeometricIntegral

/-!
# Compatibility with the original group law

The complete pointed isomorphism is a morphism of the original groups. Rigidity
proves multiplication compatibility; no transported replacement law is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve WeierstrassIntegralChart CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- The complete coordinate isomorphism bundled over the original field. -/
def projectiveOverIso : G ≅ integralCurveOver (equation G hd hc hg s hI) :=
  Over.isoMk (projectiveIso G hd hc hg s hI) (projectiveIso_over G hd hc hg s hI)

include hd hc hg s hI in
/-- The original group square is integral, via its constructed cubic presentation. -/
theorem groupSquare_isIntegral : IsIntegral (G ⊗ G).left := by
  let W := equation G hd hc hg s hI
  let _ := Chow.source_isNoetherian (integralCurveStructure W)
  let _ := integralCurveStructure_smooth_dimension W
    (equation_isElliptic G hd hc hg s hI).isUnit
  let _ : IsIntegral ((integralCurveOver W ⊗ integralCurveOver W).left) := by
    change IsIntegral (Limits.pullback (integralCurveStructure W) (integralCurveStructure W))
    infer_instance
  let e := projectiveOverIso G hd hc hg s hI
  let e₂ : (G ⊗ G).left ≅ ((integralCurveOver W ⊗ integralCurveOver W).left) :=
    (Over.forget _).mapIso (e ⊗ᵢ e)
  exact IsIntegral.of_isIso e₂.inv

/-- Use the already proved Weierstrass group law on the constructed nonsingular cubic. -/
local instance constructedCurveGroup : GrpObj (integralCurveOver (equation G hd hc hg s hI)) :=
  integralCurveGrpObj _ (equation_isElliptic G hd hc hg s hI).isUnit

/-- When the specified point is the original identity, the complete map preserves both laws. -/
theorem projectiveOverIso_isMonHom (hs : s = η[G]) :
    IsMonHom (projectiveOverIso G hd hc hg s hI).hom := by
  let _ := groupSquare_isIntegral G hd hc hg s hI
  let _ : LocallyOfFiniteType (integralCurveOver (equation G hd hc hg s hI)).hom :=
    inferInstanceAs (LocallyOfFiniteType (integralCurveStructure (equation G hd hc hg s hI)))
  let _ : IsSeparated (integralCurveOver (equation G hd hc hg s hI)).hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure (equation G hd hc hg s hI)))
  apply properGroup_isMonHom_of_one
  apply Over.OverMorphism.ext
  change η[G].left ≫ toProjective G hd hc hg s hI =
    integralCurveZero (equation G hd hc hg s hI)
  rw [← hs]
  exact toProjective_point G hd hc hg s hI

/-- Multiplication on the original whole group agrees with the established cubic addition. -/
theorem toProjective_mul (hs : s = η[G]) :
    μ[G].left ≫ toProjective G hd hc hg s hI =
      ((projectiveOverIso G hd hc hg s hI).hom ⊗ₘ
        (projectiveOverIso G hd hc hg s hI).hom).left ≫
        integralCurveAddition (equation G hd hc hg s hI)
          (equation_isElliptic G hd hc hg s hI).isUnit := by
  let _ := projectiveOverIso_isMonHom G hd hc hg s hI hs
  exact congrArg Over.Hom.left (IsMonHom.mul_hom (projectiveOverIso G hd hc hg s hI).hom)

end FLT.Mazur.GenusOneGroupCoordinates
