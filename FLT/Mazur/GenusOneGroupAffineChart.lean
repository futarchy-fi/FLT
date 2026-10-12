/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleDivisorComplementAffine
public import FLT.Mazur.GenusOneGroupCoordinateRing

/-!
# An actual affine Weierstrass chart of the original geometric group curve

The original point has degree one, hence its line is ample and its complement
is affine. The already constructed coordinate evaluation therefore identifies
that entire complement with the actual affine cubic, over the original field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GenusOneGroupCoordinates
open FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)
  (hg : curveGenus G.hom hd hc = 1)
  (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker)

/-- Use the actual complement section ring on its bundled field module. -/
local instance affineChartFunctionRing : CommRing (divisorComplementModule G.hom s.left.ker) :=
  inferInstanceAs (CommRing
    Γ((Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl), ⊤))

/-- The original point complement, as an open of the original group curve. -/
def complement : G.left.Opens := s.left.ker.support.compl

include hd in
omit [IsAlgClosed k] [GrpObj G] in
/-- Positive degree proves affineness of the actual point complement. -/
theorem complement_isAffine : IsAffineOpen (complement G s) := by
  let hI := (smoothSectionCartier G.hom s.left inferInstance inferInstance s.w).1
  apply isAffineOpen_divisorComplement G.hom hI
  apply ampleLineBundle_of_curveSheafDegree_pos G.hom hd.le
    hI.divisorLineBundle_locallyFreeRankOne
  rw [pointedCurve_line_degree_one G.hom s.left s.w]
  decide

/-- The original complement morphism is induced by the constructed coordinate functions. -/
def toAffineCubic : (complement G s).toScheme ⟶
    Spec (.of (equation G hd hc hg s hI).toAffine.CoordinateRing) :=
  (complement G s).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (coordinateEvaluation G hd hc hg s hI))

/-- The coordinate morphism preserves the original field structure map. -/
theorem toAffineCubic_over : toAffineCubic G hd hc hg s hI ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k (equation G hd hc hg s hI).toAffine.CoordinateRing)) =
        (complement G s).ι ≫ G.hom := by
  rw [toAffineCubic, Category.assoc, ← Spec.map_comp]
  change (complement G s).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((coordinateEvaluation G hd hc hg s hI).comp
      (algebraMap k (equation G hd hc hg s hI).toAffine.CoordinateRing))) = _
  rw [show (coordinateEvaluation G hd hc hg s hI).comp
      (algebraMap k (equation G hd hc hg s hI).toAffine.CoordinateRing) = scalar G s from
    WeierstrassAffineEquationEvaluation.evaluation_comp_scalar
      (equation G hd hc hg s hI) (scalar G s) _ _ (equation_holds G hd hc hg s hI)]
  simp only [scalar, structureScalarMap, CommRingCat.ofHom_hom, Spec.map_comp]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

/-- The given coordinate morphism is an isomorphism on the entire original complement. -/
theorem toAffineCubic_isIso : IsIso (toAffineCubic G hd hc hg s hI) := by
  let _ : IsAffine (complement G s).toScheme := complement_isAffine G hd s
  let _ : IsIso (CommRingCat.ofHom (coordinateEvaluation G hd hc hg s hI)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (coordinateRingEquiv G hd hc hg s hI).bijective
  unfold toAffineCubic
  infer_instance

/-- An actual affine Weierstrass chart, constructed on the original point complement. -/
def affineIso : (complement G s).toScheme ≅
    Spec (.of (equation G hd hc hg s hI).toAffine.CoordinateRing) := by
  let _ := toAffineCubic_isIso G hd hc hg s hI
  exact asIso (toAffineCubic G hd hc hg s hI)

/-- This isomorphism is over the specified original coefficient field. -/
theorem affineIso_over : (affineIso G hd hc hg s hI).hom ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k (equation G hd hc hg s hI).toAffine.CoordinateRing)) =
        (complement G s).ι ≫ G.hom :=
  toAffineCubic_over G hd hc hg s hI

end FLT.Mazur.GenusOneGroupCoordinates
