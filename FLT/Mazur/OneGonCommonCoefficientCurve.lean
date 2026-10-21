/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingCoefficientChange

/-!
# Comparing one-gon curves from independent coefficient bases

Two parameters with the same image in a common coefficient ring give an
isomorphism of the actual base-changed whole cubics over that ring. The
comparison retains the structure morphisms and the infinity sections.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] (a : A) (b : B)

/-- An abstract cancellation avoids expanding the concrete curve constructions. -/
theorem iso_common_recovery {D : Type*} [Category D] {W X Y Z : D}
    (e : W ≅ X) (f : W ≅ Y) (g : Y ≅ Z) :
    e.hom ≫ (e.symm ≪≫ f ≪≫ g).hom = f.hom ≫ g.hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- The whole-cubic coefficient comparison as an isomorphism over the common base. -/
irreducible_def coefficientCurveOverIso : family (algebraMap A C a) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj (family a) :=
  Over.isoMk (coefficientPullbackIso a) (coefficientPullbackIso_snd a)

/-- Sealed parameter transport avoids reducing equality of constructed scheme objects. -/
irreducible_def parameterCurveIso {s t : C} (h : s = t) : family s ≅ family t :=
  eqToIso (congrArg family h)

/-- Whole-cubic comparison for independent initial rings with equal recovered parameters. -/
irreducible_def commonCoefficientCurveIso (h : algebraMap A C a = algebraMap B C b) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))).obj (family a) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))).obj (family b) :=
  (coefficientCurveOverIso a).symm ≪≫ parameterCurveIso h ≪≫
    coefficientCurveOverIso b

/-- Both coefficient models identify with the same intrinsic whole cubic. -/
@[reassoc] theorem commonCoefficientCurveIso_recovery
    (h : algebraMap A C a = algebraMap B C b) :
    (coefficientCurveOverIso a).hom ≫ (commonCoefficientCurveIso a b h).hom =
      (parameterCurveIso h).hom ≫ (coefficientCurveOverIso b).hom := by
  rw [commonCoefficientCurveIso_def]
  exact iso_common_recovery _ _ _

/-- The comparison is over the actual common coefficient spectrum. -/
@[reassoc] theorem commonCoefficientCurveIso_structure
    (h : algebraMap A C a = algebraMap B C b) :
    (commonCoefficientCurveIso a b h).hom.left ≫
      pullback.snd (family b).hom (Spec.map (CommRingCat.ofHom (algebraMap B C))) =
        pullback.snd (family a).hom (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
  (commonCoefficientCurveIso a b h).hom.w

/-- Parameter transport on the full curve retains the original infinity marking. -/
@[reassoc] theorem parameterCurveIso_marking {s t : C} (h : s = t) :
    marking s ≫ ((parameterCurveIso h).hom).left = marking t := by
  subst t
  rw [parameterCurveIso_def]
  simp

/-- The two recovered infinity sections agree under the common-base comparison. -/
@[reassoc] theorem commonCoefficientCurveIso_marking
    (h : algebraMap A C a = algebraMap B C b) :
    (marking (algebraMap A C a) ≫ (coefficientCurveOverIso a).hom.left) ≫
      (commonCoefficientCurveIso a b h).hom.left =
        marking (algebraMap B C b) ≫ (coefficientCurveOverIso b).hom.left := by
  have hr := congrArg (fun f => f.left) (commonCoefficientCurveIso_recovery a b h)
  simp only [Over.comp_left] at hr
  rw [Category.assoc, hr, parameterCurveIso_marking_assoc h]

end FLT.Mazur.OneGonSmoothing
