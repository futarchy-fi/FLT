/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenusOneNonspecialPoint
public import FLT.Mazur.GroupObjectPointTranslation
public import FLT.Mazur.PointDivisorIsoCohomology

/-!
# Every original point of a geometric genus-one group curve is nonspecial

Translate the given point to the constructed nonspecial point. Pullback of the
full point divisor transports the actual cohomology, without changing the curve
or replacing its distinguished point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
namespace FLT.Mazur.FCurve
open GroupObjectPointTranslation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsIntegral G.left] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom]
  (hd : topologicalKrullDim G.left = 1) (hc : HasConstantGlobalSections G.hom)

/-- H¹ of the positive line of any specified point vanishes on the original group curve. -/
theorem genusOne_group_point_h1 (hg : curveGenus G.hom hd hc = 1)
    (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker) :
    Subsingleton (ModuleScalarH G.hom (divisorLineBundle s.left.ker hI) 1) := by
  obtain ⟨p, hJ, hp, hz, _⟩ :=
    pointed_genusOne_exists_nonspecial_point G.hom hd hc hg s.left s.w
  let t : 𝟙_ (Over (Spec (.of k))) ⟶ G := Over.homMk p hp
  let a := translationIso (t * s⁻¹)
  have ha : s ≫ a.hom = t := by
    change s ≫ translation (t * s⁻¹) = t
    rw [comp_translation]
    simp only [toUnit_unit, Category.id_comp, mul_assoc, inv_mul_cancel, mul_one]
  let e : G.left ≅ G.left := (Over.forget _).mapIso a
  have hs : s.left ≫ e.hom = p := congrArg (fun z ↦ z.left) ha
  let d := pointDivisorScalarHIsoEquiv e G.hom G.hom a.hom.w
    s.left p s.w hp hs hI hJ 1
  let _ := hz
  exact d.symm.injective.subsingleton

/-- The original point line has exactly one global section, with its original field action. -/
theorem genusOne_group_point_h0 (hg : curveGenus G.hom hd hc = 1)
    (s : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hI : EffectiveCartier s.left.ker) :
    Module.finrank k (ModuleScalarH G.hom (divisorLineBundle s.left.ker hI) 0) = 1 := by
  let _ := genusOne_group_point_h1 G hd hc hg s hI
  have he := curve_h0_eq_of_h1_vanishing G.hom hd hc (divisorLineBundle s.left.ker hI)
  rw [pointedCurve_line_degree_one G.hom s.left s.w, hg] at he
  omega

end FLT.Mazur.FCurve
