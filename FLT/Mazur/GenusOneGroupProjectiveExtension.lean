/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupAffineChart
public import FLT.Mazur.ProperDenseOpenExtension
public import FLT.Mazur.SmoothCurveValuationStalk
public import FLT.Mazur.WeierstrassIntegralProper
public import FLT.Mazur.WeierstrassMonicOpenImmersion

/-!
# Extension of the original coordinates to the proper cubic

The actual smooth curve has valuation stalks. Properness of the target extends
the already constructed affine coordinate morphism uniquely across its point.
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

/-- The original affine coordinates viewed in the whole projective cubic. -/
def affineToProjective : (complement G s).toScheme ⟶
    integralCurve (equation G hd hc hg s hI) :=
  toAffineCubic G hd hc hg s hI ≫ monicToIntegralCurve _

/-- The affine map into the proper model retains the original field morphism. -/
theorem affineToProjective_over : affineToProjective G hd hc hg s hI ≫
    integralCurveStructure (equation G hd hc hg s hI) = (complement G s).ι ≫ G.hom := by
  rw [affineToProjective, Category.assoc, monicToIntegralCurve_over]
  exact toAffineCubic_over G hd hc hg s hI

include hd hc hg hI in
/-- The original point complement is dense. -/
theorem complement_dense : Dense ((complement G s) : Set G.left) := by
  let e := affineIso G hd hc hg s hI
  obtain ⟨z⟩ := (inferInstance : Nonempty
    (Spec (.of (equation G hd hc hg s hI).toAffine.CoordinateRing)))
  exact (complement G s).2.dense ⟨(e.inv z).1, (e.inv z).2⟩

/-- The original affine coordinate map extends uniquely across the specified point. -/
theorem existsUnique_projectiveExtension :
    ∃! f : G.left ⟶ integralCurve (equation G hd hc hg s hI),
      f ≫ integralCurveStructure (equation G hd hc hg s hI) = G.hom ∧
      (complement G s).ι ≫ f = affineToProjective G hd hc hg s hI := by
  let _ : G.left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from G.hom]
    infer_instance
  let _ : ∀ z : G.left, ValuationRing (G.left.presheaf.stalk z) :=
    fun z ↦ smoothCurve_stalk_valuationRing G.hom z
  exact existsUnique_denseOpen_extension_of_valuation_stalks G.hom _ _
    (complement_dense G hd hc hg s hI) _ (affineToProjective_over G hd hc hg s hI)

/-- The proper extension of the actual original coordinate functions. -/
def toProjective : G.left ⟶ integralCurve (equation G hd hc hg s hI) :=
  (existsUnique_projectiveExtension G hd hc hg s hI).choose

/-- The extension keeps the specified original field map. -/
theorem toProjective_over : toProjective G hd hc hg s hI ≫
    integralCurveStructure (equation G hd hc hg s hI) = G.hom :=
  (existsUnique_projectiveExtension G hd hc hg s hI).choose_spec.1.1

/-- On the original complement the extension is exactly the constructed affine map. -/
theorem toProjective_restrict : (complement G s).ι ≫ toProjective G hd hc hg s hI =
    affineToProjective G hd hc hg s hI :=
  (existsUnique_projectiveExtension G hd hc hg s hI).choose_spec.1.2

end FLT.Mazur.GenusOneGroupCoordinates
