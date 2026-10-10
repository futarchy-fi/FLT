/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineSlopeNormalization

/-!
# The original full infinity chart after ordered normalization

On the right affine chart normalization is w ↦ a*w+1. Consequently the
original translated Laurent chart becomes the standard torus with reciprocal
left coordinate. These are equalities on the full schemes and all functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (a : Kˣ)

/-- The full right affine coordinate transforms by w ↦ a*w+1 over every test ring. -/
@[reassoc] theorem slopeNormalization_right_point {S : Type u} [CommRing S]
    (f : K →+* S) (w : S) :
    (Spec.map (CommRingCat.ofHom (eval₂RingHom f w)) ≫ right K) ≫
        (slopeNormalizationIso a).hom =
      Spec.map (CommRingCat.ofHom (eval₂RingHom f (f a * w + 1))) ≫ right K := by
  have h := slopeNormalization_point a f (fun i => (![w, 1] : Fin 2 → S) i.down)
    (ULift.up 1) (ULift.up 1) 1 1 rfl rfl
  rw [homogeneousPoint_right, homogeneousPoint_right] at h
  simpa only [inv_one, Units.val_one, one_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] using h

/-- The normalization has the specified polynomial map on the entire right chart. -/
@[reassoc] theorem slopeNormalization_right :
    right K ≫ (slopeNormalizationIso a).hom =
      Spec.map (CommRingCat.ofHom (aeval (C (a : K) * X + 1)).toRingHom) ≫ right K := by
  have h := slopeNormalization_right_point a (C : K →+* K[X]) X
  have hi : eval₂RingHom (C : K →+* K[X]) X = RingHom.id _ := by
    ext <;> simp
  have he : eval₂RingHom (C : K →+* K[X]) (C (a : K) * X + 1) =
      (aeval (C (a : K) * X + 1)).toRingHom := by
    ext <;> simp
  rw [hi, he] at h
  simpa only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] using h

/-- The original full Laurent chart becomes the standard torus in the right coordinate. -/
@[reassoc] theorem slopeNormalization_infinityTorus :
    infinityTorusChart a ≫ (slopeNormalizationIso a).hom = overlapLeft K ≫ right K := by
  have h := slopeNormalization_right_point a (LaurentPolynomial.C : K →+* K[T;T⁻¹])
    (LaurentPolynomial.C (↑a⁻¹ : K) * (LaurentPolynomial.T 1 - 1))
  have he : LaurentPolynomial.C (a : K) *
      (LaurentPolynomial.C (↑a⁻¹ : K) * (LaurentPolynomial.T 1 - 1)) + 1 =
        LaurentPolynomial.T (R := K) 1 := by
    rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul, sub_add_cancel]
  rw [he] at h
  have ht : eval₂RingHom (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (LaurentPolynomial.T 1) =
      Polynomial.toLaurent := by
    ext <;> simp
  rw [ht] at h
  exact h

/-- The left coordinate of the normalized full torus is the inverse Laurent generator. -/
@[reassoc] theorem slopeNormalization_infinityTorus_left :
    infinityTorusChart a ≫ (slopeNormalizationIso a).hom =
      overlapRight K ≫ left K := by
  rw [slopeNormalization_infinityTorus]
  have h := overlap_condition K
  have hi : (inversion K).hom ≫ (inversion K).hom = 𝟙 _ :=
    (inversion K).hom_inv_id
  calc
    overlapLeft K ≫ right K = (inversion K).hom ≫ overlapRight K ≫ right K := by
      simp only [overlapRight, ← Category.assoc, hi, Category.id_comp]
    _ = (inversion K).hom ≫ overlapLeft K ≫ left K := by rw [h]
    _ = overlapRight K ≫ left K := by rw [overlapRight, Category.assoc]

end FLT.Mazur.ProjectiveLine
