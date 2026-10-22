/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineEvaluationNaturality

/-!
# Actual evaluation squares for a full variable change over a fixed ring

The scalar and two coordinate values determine the complete affine evaluation
square. Its spectrum statement applies even to nonaffine source schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineVariableChangeMap

/-- The full variable substitution is detected by original scalars and coordinate values. -/
theorem changedEvaluation_eq {R A : Type*} [CommRing R] [CommRing A]
    (W V : WeierstrassCurve R) (C : VariableChange R) (hC : C • W = V)
    (φ : R →+* A) (p : Coordinate V 2 →+* A) (q : Coordinate W 2 →+* A)
    (hp : ∀ r, p (algebraMap R _ r) = φ r)
    (hq : ∀ r, q (algebraMap R _ r) = φ r)
    (hx : φ (C.u : R) ^ 2 * p (coord V 2 0) + φ C.r = q (coord W 2 0))
    (hy : φ (C.u : R) ^ 3 * p (coord V 2 1) +
      φ (C.u : R) ^ 2 * φ C.s * p (coord V 2 0) + φ C.t = q (coord W 2 1)) :
    p.comp (affineVariableChangeMap W V C hC).toRingHom = q := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change p (affineVariableChangeMap W V C hC (algebraMap R _ r)) = q (algebraMap R _ r)
    rw [AlgHom.commutes, hp, hq]
  · intro i
    change p (affineVariableChangeMap W V C hC (coord W 2 i)) = q (coord W 2 i)
    fin_cases i
    · change p (affineVariableChangeMap W V C hC (coord W 2 0)) = q (coord W 2 0)
      simpa only [affineVariableChangeMap_x, map_add, map_mul, map_pow, hp] using hx
    · change p (affineVariableChangeMap W V C hC (coord W 2 1)) = q (coord W 2 1)
      simpa only [affineVariableChangeMap_y, map_add, map_mul, map_pow, hp] using hy
    · change p (affineVariableChangeMap W V C hC (coord W 2 2)) = q (coord W 2 2)
      simp only [coord_self, map_one]

/-- A ring evaluation square gives the actual scheme square without expanding quotient rings. -/
theorem coordinateRingEvaluation_two_square {X Y : Scheme} (π : X ⟶ Y)
    {A B : Type} [CommRing A] [CommRing B]
    (d : A →+* B) (p : B →+* Γ(X, ⊤)) (q : A →+* Γ(Y, ⊤))
    (h : p.comp d = π.appTop.hom.comp q) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom p)) ≫ Spec.map (CommRingCat.ofHom d) =
      π ≫ Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q) := by
  have hh : CommRingCat.ofHom d ≫ CommRingCat.ofHom p =
      CommRingCat.ofHom q ≫ π.appTop := CommRingCat.hom_ext h
  rw [Category.assoc, ← Spec.map_comp, hh, Spec.map_comp,
    ← Scheme.toSpecΓ_naturality_assoc]

/-- Full affine coordinate comparison is natural for the original evaluation morphisms. -/
theorem affineEvaluation_variable_square {R : Type} [CommRing R]
    {X Y : Scheme} (π : X ⟶ Y) (W V : WeierstrassCurve R)
    (C : VariableChange R) (hC : C • W = V)
    (p : Coordinate V 2 →+* Γ(X, ⊤)) (q : Coordinate W 2 →+* Γ(Y, ⊤))
    (h : p.comp (affineVariableChangeMap W V C hC).toRingHom = π.appTop.hom.comp q) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom p)) ≫
      (affineVariableChangeIso W V C hC).hom =
        π ≫ Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q) := by
  rw [affineVariableChangeIso_hom_ringMap]
  exact coordinateRingEvaluation_two_square π (affineVariableChangeMap W V C hC).toRingHom p q h

end FLT.Mazur.WeierstrassIntegralChart
