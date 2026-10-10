/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedParameter
public import FLT.Mazur.WeierstrassEquationTransport

/-!
# Exact coefficient and chart maps of the normalized cubic

The coefficient group comparison includes an equation equality transport.
Retain that transport explicitly and identify the map on every affine chart,
including each original coordinate generator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Equality transport followed by a group comparison retains both underlying scheme maps. -/
theorem equationGroupComparison_left {A : Type} [CommRing A]
    {W V : WeierstrassCurve A} (h : W = V) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
    (hg : integralCurveGroup W hW = integralCurveGroup V hV)
    {H : CommGrp (Over (Spec (.of A)))} (e : integralCurveGroup V hV ≅ H) :
    (eqToIso hg ≪≫ e).hom.hom.hom.hom.left =
      eqToHom (congrArg integralCurve h) ≫ e.hom.hom.hom.hom.left := by
  subst V
  change e.hom.hom.hom.hom.left = 𝟙 _ ≫ e.hom.hom.hom.hom.left
  exact (Category.id_comp _).symm

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- The normalized group comparison retains its actual equation equality transport. -/
theorem auxiliaryNormalizedCoefficientGroupIso_hom :
    let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
    (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left =
      eqToHom (congrArg integralCurve (auxiliaryNormalizedCoefficientHom_equation g).symm) ≫
        (integralCurveCoefficientBaseChangeIso smoothEquation).hom := by
  let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
  dsimp only
  have he : auxiliaryNormalizedEquation g = smoothEquation.map (algebraMap ParameterRing R) :=
    (auxiliaryNormalizedCoefficientHom_equation g).symm
  have hd : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ :=
    he ▸ auxiliaryNormalizedEquation_discriminant g
  have hg : integralCurveGroup (auxiliaryNormalizedEquation g)
      (auxiliaryNormalizedEquation_discriminant g) =
        integralCurveGroup (smoothEquation.map (algebraMap ParameterRing R)) hd := by
    congr 1
  exact equationGroupComparison_left he (auxiliaryNormalizedEquation_discriminant g) hd hg
    (integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hd)

/-- Projection retains both the equality transport and the original coefficient morphism. -/
@[reassoc] theorem auxiliaryNormalizedCoefficientGroupIso_fst :
    let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
    (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
      pullback.fst (integralCurveStructure smoothEquation)
        (auxiliaryNormalizedCoefficientBase g) =
          eqToHom (congrArg integralCurve
            (auxiliaryNormalizedCoefficientHom_equation g).symm) ≫
              integralCoefficientMorphism (S := R) smoothEquation := by
  let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
  dsimp only
  rw [auxiliaryNormalizedCoefficientGroupIso_hom, Category.assoc]
  exact congrArg (fun k => eqToHom (congrArg integralCurve
    (auxiliaryNormalizedCoefficientHom_equation g).symm) ≫ k)
      (integralCurveCoefficientBaseChangeIso_fst (S := R) smoothEquation)

/-- The actual universal coordinate map into the normalized affine chart. -/
def auxiliaryNormalizedChartMap (j : Fin 3) :
    Coordinate smoothEquation j →+* Coordinate (auxiliaryNormalizedEquation g) j := by
  let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
  exact (chartEquationMap (auxiliaryNormalizedCoefficientHom_equation g) j).toRingHom.comp
    (chartCoefficientMap (S := R) smoothEquation j).toRingHom

/-- Every original chart coordinate remains its normalized coordinate generator. -/
theorem auxiliaryNormalizedChartMap_coord (j i : Fin 3) :
    auxiliaryNormalizedChartMap g j (coord smoothEquation j i) =
      coord (auxiliaryNormalizedEquation g) j i := by
  let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
  change chartEquationMap (auxiliaryNormalizedCoefficientHom_equation g) j
    (chartCoefficientMap (S := R) smoothEquation j (coord smoothEquation j i)) = _
  rw [chartCoefficientMap_coord (S := R)]
  exact chartEquationMap_coord (auxiliaryNormalizedCoefficientHom_equation g) j i

/-- Each chart square uses the actual normalized group comparison and original projection. -/
@[reassoc] theorem auxiliaryNormalizedChartMap_chart (j : Fin 3) :
    Spec.map (CommRingCat.ofHom (auxiliaryNormalizedChartMap g j)) ≫
      integralCurveChart smoothEquation j =
        integralCurveChart (auxiliaryNormalizedEquation g) j ≫
          (auxiliaryNormalizedCoefficientGroupIso g).hom.hom.hom.hom.left ≫
            pullback.fst (integralCurveStructure smoothEquation)
              (auxiliaryNormalizedCoefficientBase g) := by
  let _ : Algebra ParameterRing R := (auxiliaryNormalizedCoefficientHom g).toAlgebra
  rw [auxiliaryNormalizedCoefficientGroupIso_fst]
  change Spec.map (CommRingCat.ofHom (chartCoefficientMap (S := R) smoothEquation j).toRingHom ≫
    CommRingCat.ofHom
      (chartEquationMap (auxiliaryNormalizedCoefficientHom_equation g) j).toRingHom) ≫ _ = _
  have hc := integralCurveChart_coefficientMorphism (S := R) smoothEquation j
  change _ = Spec.map (CommRingCat.ofHom
    (chartCoefficientMap (S := R) smoothEquation j).toRingHom) ≫ _ at hc
  rw [Spec.map_comp, Category.assoc, ← hc, ← Category.assoc]
  exact (congrArg (fun k => k ≫ integralCoefficientMorphism (S := R) smoothEquation)
    (integralCurveChart_equation_symm
      (auxiliaryNormalizedCoefficientHom_equation g).symm j)).trans (Category.assoc _ _ _)

end FLT.Mazur.UniversalWeierstrass
