/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassCoefficientZero

/-!
# The actual projection from a specified local generic equation

The specified variable change followed by coefficient projection is Cartesian.
It detects maps with a fixed structure morphism and pulls the original zero
section back to the exact local zero section.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L R : Type} [CommRing K] [CommRing L] [CommRing R]
  [Algebra K L] [Algebra R L]
  (E : WeierstrassCurve K) (W : WeierstrassCurve R) (C : VariableChange L)
  (hC : C • E.map (algebraMap K L) = W.map (algebraMap R L))

/-- The actual projection retaining the specified generic coordinate change. -/
def localGenericProjection : integralCurve (W.map (algebraMap R L)) ⟶ integralCurve E :=
  (integralVariableChangeIso _ _ C hC).hom ≫ integralCoefficientMorphism E

/-- The local projection respects the original coefficient map. -/
@[reassoc] theorem localGenericProjection_structure :
    localGenericProjection E W C hC ≫ integralCurveStructure E =
      integralCurveStructure (W.map (algebraMap R L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [localGenericProjection, Category.assoc, integralCoefficientMorphism_structure,
    ← Category.assoc]
  exact congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (integralVariableChangeTo_structure _ _ C hC)

/-- The original curve is recovered by the exact Cartesian coefficient square. -/
theorem localGenericProjection_isPullback :
    IsPullback (localGenericProjection E W C hC)
      (integralCurveStructure (W.map (algebraMap R L))) (integralCurveStructure E)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have H : IsPullback (integralVariableChangeIso _ _ C hC).hom
      (integralCurveStructure (W.map (algebraMap R L)))
      (integralCurveStructure (E.map (algebraMap K L))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact integralVariableChangeTo_structure _ _ C hC⟩
  simpa only [localGenericProjection, Category.id_comp] using
    H.paste_horiz (integralCoefficient_isPullback E)

/-- The projection detects maps once their local structure morphisms are fixed. -/
theorem localGenericProjection_hom_ext {T : Scheme}
    (f g : T ⟶ integralCurve (W.map (algebraMap R L)))
    (h : f ≫ localGenericProjection E W C hC = g ≫ localGenericProjection E W C hC)
    (hs : f ≫ integralCurveStructure (W.map (algebraMap R L)) =
      g ≫ integralCurveStructure (W.map (algebraMap R L))) : f = g :=
  (localGenericProjection_isPullback E W C hC).hom_ext h hs

/-- The original zero is retained by both the coordinate change and coefficient map. -/
@[reassoc] theorem localGenericProjection_zero :
    integralCurveZero (W.map (algebraMap R L)) ≫ localGenericProjection E W C hC =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ integralCurveZero E := by
  rw [localGenericProjection, ← Category.assoc, integralVariableChangeIso_zero,
    integralCoefficientMorphism_zero]

/-- The original identity fiber pulls back to the specified local identity section. -/
theorem localGenericProjection_zero_isPullback :
    IsPullback (integralCurveZero (W.map (algebraMap R L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (localGenericProjection E W C hC) (integralCurveZero E) := by
  have H : IsPullback
      (integralCurveZero (W.map (algebraMap R L)) ≫
        integralCurveStructure (W.map (algebraMap R L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))
      (integralCurveZero E ≫ integralCurveStructure E) := by
    simp only [integralCurveZero_structure]
    exact IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.comp_id]⟩
  exact H.of_right (localGenericProjection_zero E W C hC)
    (localGenericProjection_isPullback E W C hC).flip

end FLT.Mazur.WeierstrassIntegralChart
