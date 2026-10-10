/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineHomogeneousCoordinates
public import FLT.Mazur.ProjectiveLineSlopeNormalizationLinear
public import FLT.Mazur.ProjectiveLineInfinityTorusMarks

/-!
# Normalizing the original ordered slope markings

The actual projective automorphism q=v/(v+a) takes the markings 0 and -a
to zero and infinity, in that order, and preserves the coefficient projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.ProjectiveLine
open ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- Ordered normalization of the slope markings on the actual glued projective line. -/
def slopeNormalizationIso : scheme K ≅ scheme K :=
  homogeneousIso K ≪≫ slopeNormalizationProjIso a ≪≫ (homogeneousIso K).symm

/-- The normalization is an automorphism over the original coefficient field. -/
@[reassoc] theorem slopeNormalizationIso_base :
    (slopeNormalizationIso a).hom ≫ toBase K = toBase K := by
  simp only [slopeNormalizationIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    homogeneousIso_inv_base, slopeNormalizationProjIso_base, homogeneousIso_base]

/-- Original affine slope markings have homogeneous coordinates [1:c]. -/
@[reassoc] theorem infinitySlopeMark_homogeneous (c : K) :
    infinitySlopeMark c ≫ (homogeneousIso K).hom =
      unitChartPoint K (ULift.{u} (Fin 2)) (.id K)
        (fun i => ![1, c] i.down) (ULift.up 0) 1 rfl := by
  apply (cancel_mono (homogeneousIso K).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, homogeneousPoint_left]
  simp only [inv_one, Units.val_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul]
  rfl

/-- The normalization on all affine test points is the full homogeneous substitution. -/
@[reassoc] theorem slopeNormalization_point {S : Type u} [CommRing S]
    (f : K →+* S) (x : ULift.{u} (Fin 2) → S)
    (i j : ULift.{u} (Fin 2)) (b c : Sˣ) (hi : x i = b)
    (hj : (![f a * x (ULift.up 0) + x (ULift.up 1), x (ULift.up 1)] : Fin 2 → S)
      j.down = c) :
    (unitChartPoint K (ULift.{u} (Fin 2)) f x i b hi ≫ (homogeneousIso K).inv) ≫
        (slopeNormalizationIso a).hom =
      unitChartPoint K (ULift.{u} (Fin 2)) f
        (fun k => ![f a * x (ULift.up 0) + x (ULift.up 1), x (ULift.up 1)] k.down)
        j c hj ≫ (homogeneousIso K).inv := by
  simp only [slopeNormalizationIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc]
  congr 1
  exact unitChartPoint_linearIso_of_eval (slopeNormalizationLinear a).symm f x _
    (slopeNormalization_evaluation a f x) i j b c hi hj

/-- The first original marking is taken to the polygon's zero endpoint. -/
@[reassoc] theorem slopeNormalization_first :
    infinitySlopeMark (0 : K) ≫ (slopeNormalizationIso a).hom = zero K := by
  have h := slopeNormalization_point a (.id K)
    (fun i => (![1, 0] : Fin 2 → K) i.down) (ULift.up 0) (ULift.up 0) 1 a rfl
    (by simp)
  rw [← infinitySlopeMark_homogeneous] at h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  rw [homogeneousPoint_left] at h
  simpa only [Units.val_inv_eq_inv_val, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    mul_zero, zero, chartZero, Polynomial.evalRingHom] using h

/-- The second original marking is taken to the polygon's infinity endpoint. -/
@[reassoc] theorem slopeNormalization_second :
    infinitySlopeMark (-(a : K)) ≫ (slopeNormalizationIso a).hom = infinity K := by
  have h := slopeNormalization_point a (.id K)
    (fun i => (![1, -(a : K)] : Fin 2 → K) i.down)
    (ULift.up 0) (ULift.up 1) 1 (-a) rfl (by simp)
  rw [← infinitySlopeMark_homogeneous] at h
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  rw [homogeneousPoint_right] at h
  simpa only [RingHom.id_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one, add_neg_cancel, mul_zero, infinity, chartZero,
    Polynomial.evalRingHom] using h

/-- The inverse normalization retains the coefficient projection. -/
@[reassoc] theorem slopeNormalizationIso_inv_base :
    (slopeNormalizationIso a).inv ≫ toBase K = toBase K := by
  rw [← slopeNormalizationIso_base a, Iso.inv_hom_id_assoc, slopeNormalizationIso_base]

/-- The polygon zero endpoint recovers exactly the first original slope marking. -/
@[reassoc] theorem slopeNormalization_inv_zero :
    zero K ≫ (slopeNormalizationIso a).inv = infinitySlopeMark (0 : K) := by
  rw [← slopeNormalization_first a, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The polygon infinity endpoint recovers exactly the second original slope marking. -/
@[reassoc] theorem slopeNormalization_inv_infinity :
    infinity K ≫ (slopeNormalizationIso a).inv = infinitySlopeMark (-(a : K)) := by
  rw [← slopeNormalization_second a, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.ProjectiveLine
