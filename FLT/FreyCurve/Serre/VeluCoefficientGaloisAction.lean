/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffinePointNaturality
public import FLT.Mazur.WeierstrassCoefficientFieldCover

/-!
# The Galois action on the original coefficient-extended cubic

The action is constructed using the actual Cartesian coefficient square.
Its projection to the original cubic is fixed, and its values on the original
affine scheme points retain the classical Galois action.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  (E : WeierstrassCurve K) (g : L ≃ₐ[K] L)

local notation "EL" => E.map (algebraMap K L)

omit E in
/-- The original coefficient spectrum map is fixed by every relative field automorphism. -/
@[reassoc] theorem galoisSpec_coefficient :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext g.commutes)

/-- Galois acts on the actual extended cubic through its coefficient pullback square. -/
def integralGaloisMap : integralCurve EL ⟶ integralCurve EL :=
  (integralCoefficient_isPullback E).lift (integralCoefficientMorphism E)
    (integralCurveStructure EL ≫ Spec.map (CommRingCat.ofHom g.toRingHom)) (by
      rw [integralCoefficientMorphism_structure, Category.assoc, galoisSpec_coefficient])

/-- The action fixes the original cubic projection literally. -/
@[reassoc] theorem integralGaloisMap_coefficient :
    integralGaloisMap E g ≫ integralCoefficientMorphism E = integralCoefficientMorphism E :=
  (integralCoefficient_isPullback E).lift_fst _ _ _

/-- On the coefficient field this is the original spectrum automorphism. -/
@[reassoc] theorem integralGaloisMap_structure :
    integralGaloisMap E g ≫ integralCurveStructure EL =
      integralCurveStructure EL ≫ Spec.map (CommRingCat.ofHom g.toRingHom) :=
  (integralCoefficient_isPullback E).lift_snd _ _ _

/-- The inverse field automorphism gives an actual inverse cubic morphism. -/
theorem integralGaloisMap_inverse : integralGaloisMap E g ≫ integralGaloisMap E g.symm =
    𝟙 (integralCurve EL) := by
  apply (integralCoefficient_isPullback E).hom_ext
  · rw [Category.assoc, integralGaloisMap_coefficient, integralGaloisMap_coefficient,
      Category.id_comp]
  · rw [Category.assoc, integralGaloisMap_structure, integralGaloisMap_structure_assoc,
      Category.id_comp, ← Spec.map_comp]
    have he : CommRingCat.ofHom g.symm.toRingHom ≫ CommRingCat.ofHom g.toRingHom =
        𝟙 (CommRingCat.of L) := by
      ext x
      exact g.apply_symm_apply x
    rw [he, Spec.map_id, Category.comp_id]

/-- The actual coefficient Galois map is a scheme automorphism. -/
def integralGaloisIso : integralCurve EL ≅ integralCurve EL where
  hom := integralGaloisMap E g
  inv := integralGaloisMap E g.symm
  hom_inv_id := integralGaloisMap_inverse E g
  inv_hom_id := integralGaloisMap_inverse E g.symm

variable [DecidableEq L]

/-- The original affine point comparison carries the actual semilinear action. -/
@[reassoc] theorem integralGaloisMap_point (P : (EL).toAffine.Point) :
    (affineSmoothPoint EL (Affine.Point.map (W' := E.toAffine) g.toAlgHom P) ≫
        (integralSmoothOpen EL).ι) ≫ integralGaloisMap E g =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (affineSmoothPoint EL P ≫ (integralSmoothOpen EL).ι) := by
  apply (integralCoefficient_isPullback E).hom_ext
  · rw [Category.assoc, integralGaloisMap_coefficient, affineSmoothPoint_coefficient,
      Category.assoc, affineSmoothPoint_coefficient]
    exact (affineSmoothPoint_natural E g.toAlgHom P).symm
  · rw [Category.assoc, integralGaloisMap_structure]
    have hp (Q : (EL).toAffine.Point) :
        (affineSmoothPoint EL Q ≫ (integralSmoothOpen EL).ι) ≫
          integralCurveStructure EL = 𝟙 _ := by
      rw [Category.assoc]
      change affineSmoothPoint EL Q ≫ integralSmoothStructure EL = _
      rw [affineSmoothPoint_structure]
      exact Spec.map_id _
    rw [← Category.assoc, hp, Category.id_comp, Category.assoc, hp, Category.comp_id]

end WeierstrassCurve.Velu
