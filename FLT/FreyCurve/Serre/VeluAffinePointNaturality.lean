/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineSmoothCoordinates
public import FLT.Mazur.WeierstrassCoefficientZero
public import FLT.Mazur.WeierstrassProjectivePointNaturality

/-!
# Original affine scheme points commute with coefficient maps

Both algebra homomorphisms of point fields and projection from the extended
cubic retain the original affine coordinates and the original infinity section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L M : Type} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] (E : WeierstrassCurve K)

/-- Original affine scheme points commute with every map of coefficient fields. -/
@[reassoc] theorem affineSmoothPoint_natural [DecidableEq L] [DecidableEq M] (f : L →ₐ[K] M)
    (P : (E.map (algebraMap K L)).toAffine.Point) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) =
      affineSmoothPoint E (Affine.Point.map (W' := E.toAffine) f P) ≫
        (integralSmoothOpen E).ι := by
  cases P with
  | zero =>
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (affineSmoothPoint E (0 : (E.map (algebraMap K L)).toAffine.Point) ≫ _) =
        affineSmoothPoint E (0 : (E.map (algebraMap K M)).toAffine.Point) ≫ _
    rw [affineSmoothPoint_zero, affineSmoothPoint_zero, ← Spec.map_comp_assoc]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext f.commutes)
  | some x y h =>
    rw [Affine.Point.map_some, affineSmoothPoint_some, affineSmoothPoint_some]
    have hc : f ∘ ![x, y, 1] = ![f x, f y, 1] := by
      funext i
      fin_cases i <;> simp
    simpa only [hc] using integralChartPoint_natural E 2 ![x, y, 1]
      ((Projective.equation_some x y).mpr h.1) rfl f (by
        rw [hc]
        exact (Projective.equation_some _ _).mpr
          ((E.toAffine.baseChange_nonsingular f.injective x y).mpr h).1) (by simp)

/-- Projection from the extended cubic retains each original field-valued affine point. -/
@[reassoc] theorem affineSmoothPoint_coefficient
    (P : (E.map (algebraMap K L)).toAffine.Point) :
    (affineSmoothPoint (E.map (algebraMap K L)) P ≫
        (integralSmoothOpen (E.map (algebraMap K L))).ι) ≫
          integralCoefficientMorphism E =
      affineSmoothPoint E P ≫ (integralSmoothOpen E).ι := by
  cases P with
  | zero =>
    change (affineSmoothPoint (E.map (algebraMap K L))
      (0 : ((E.map (algebraMap K L)).map (algebraMap L L)).toAffine.Point) ≫ _) ≫ _ = _
    rw [affineSmoothPoint_zero]
    change (Spec.map (𝟙 (CommRingCat.of L)) ≫ _) ≫ _ = _
    rw [Spec.map_id, Category.id_comp, integralCoefficientMorphism_zero]
    exact (affineSmoothPoint_zero E).symm
  | some x y h =>
    rw [affineSmoothPoint_some, affineSmoothPoint_some, integralChartPoint,
      integralChartPoint, Category.assoc, integralCurveChart_coefficientMorphism,
      ← Category.assoc]
    congr 1
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg (fun f : Coordinate E 2 →+* L ↦ Spec.map (CommRingCat.ofHom f))
    change (((evaluation (E.map (algebraMap K L)) 2 ![x, y, 1]
      ((Projective.equation_some x y).mpr h.1) rfl).restrictScalars K).comp
        (chartCoefficientMap E 2)).toRingHom =
      (evaluation E 2 ![x, y, 1] ((Projective.equation_some x y).mpr h.1) rfl).toRingHom
    apply congrArg AlgHom.toRingHom
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      chartCoefficientMap_coord, evaluation_coord]

end WeierstrassCurve.Velu
