/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneGroupAffineChart
public import FLT.Mazur.WeierstrassAffineSmoothDiscriminant

/-!
# Nonsingularity of the original geometric group's equation

The constructed affine isomorphism transports smoothness from the original
curve. The affine singularity obstruction proves that its discriminant is a unit.
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

/-- The constructed monic affine cubic is smooth over the original field. -/
theorem monic_smooth : Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap k (equation G hd hc hg s hI).toAffine.CoordinateRing))) := by
  let _ := SmoothOfRelativeDimension.smooth 1 G.hom
  let e := affineIso G hd hc hg s hI
  have he := affineIso_over G hd hc hg s hI
  have hu : Smooth (e.inv ≫ (complement G s).ι ≫ G.hom) := inferInstance
  rw [← he, Iso.inv_hom_id_assoc] at hu
  exact hu

/-- The equation constructed from the original pole functions is elliptic. -/
theorem equation_isElliptic : (equation G hd hc hg s hI).IsElliptic := by
  let _ := monic_smooth G hd hc hg s hI
  exact WeierstrassIntegralChart.isElliptic_of_smooth_monic _

/-- The original coefficient discriminant is nonzero, in every characteristic. -/
theorem equation_discriminant_ne_zero : (equation G hd hc hg s hI).Δ ≠ 0 := by
  let _ := equation_isElliptic G hd hc hg s hI
  exact isUnit_iff_ne_zero.mp (WeierstrassCurve.isUnit_Δ _)

end FLT.Mazur.GenusOneGroupCoordinates
