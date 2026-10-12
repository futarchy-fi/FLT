/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupNonsingular
public import FLT.Mazur.GenusOneGroupProjectiveExtension
public import FLT.Mazur.ProperDenseOpenIso
public import FLT.Mazur.WeierstrassIntegralDomain
public import FLT.Mazur.WeierstrassIntegralSmooth

/-!
# The original geometric group curve is its complete cubic

The smooth proper cubic and the original curve have a common dense affine open.
Valuation-stalk extension constructs an inverse to the original coordinate map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- The actual extended coordinate map is an isomorphism on the whole original curve. -/
theorem toProjective_isIso : IsIso (toProjective G hd hc hg s hI) := by
  let W := equation G hd hc hg s hI
  let U := complement G s
  let _ : G.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from G.hom]
    infer_instance
  let _ : W.IsElliptic := equation_isElliptic G hd hc hg s hI
  let _ := integralCurveStructure_smooth_dimension W (WeierstrassCurve.isUnit_Δ W)
  let _ : (integralCurve W).IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from (integralCurveStructure W)]
    infer_instance
  let _ : ∀ z : integralCurve W, ValuationRing ((integralCurve W).presheaf.stalk z) :=
    fun z ↦ smoothCurve_stalk_valuationRing (integralCurveStructure W) z
  let _ : IsDominant U.ι := Opens.isDominant_ι (complement_dense G hd hc hg s hI)
  let _ : IsDominant (integralCurveChart W 2) := ⟨integralCurveAffine_denseRange W⟩
  let _ : IsDominant (monicToIntegralCurve W) := by
    unfold monicToIntegralCurve
    infer_instance
  let _ := toAffineCubic_isIso G hd hc hg s hI
  let _ : IsOpenImmersion (affineToProjective G hd hc hg s hI) := by
    unfold affineToProjective
    infer_instance
  let _ : IsDominant (affineToProjective G hd hc hg s hI) := by
    unfold affineToProjective
    infer_instance
  exact isIso_of_common_denseOpen G.hom (integralCurveStructure W) U.ι
    (affineToProjective G hd hc hg s hI) _ (toProjective_over G hd hc hg s hI)
    (toProjective_restrict G hd hc hg s hI)

/-- A complete presentation retaining the constructed original coordinate functions. -/
def projectiveIso : G.left ≅ integralCurve (equation G hd hc hg s hI) := by
  let _ := toProjective_isIso G hd hc hg s hI
  exact asIso (toProjective G hd hc hg s hI)

/-- The complete presentation preserves the original field map. -/
theorem projectiveIso_over : (projectiveIso G hd hc hg s hI).hom ≫
    integralCurveStructure (equation G hd hc hg s hI) = G.hom :=
  toProjective_over G hd hc hg s hI

end FLT.Mazur.GenusOneGroupCoordinates
