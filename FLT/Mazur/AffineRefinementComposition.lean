/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRefinementIdentity
public import FLT.Mazur.AffineRefinementCoactionCompatibility
public import FLT.Mazur.SchemePullbackCompositeRecognition

/-!
# Composition charts for affine refinement

Both base and cover charts include the equality between the spectrum of a
ring composite and the composite spectrum maps. Successive reconstruction
agrees with direct reconstruction after these charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual sheaf pullback composition chart for two ring maps. -/
def compositionChart {R R' R'' : CommRingCat.{u}} (a : R ⟶ R') (c : R' ⟶ R'')
    (A : (Spec R).Modules) :
    (pullback (Spec.map c)).obj ((pullback (Spec.map a)).obj A) ≅
      (pullback (Spec.map (a ≫ c))).obj A :=
  SchemePullbackSquare.compositionChart (Spec.map c) (Spec.map a)
    (Spec.map (a ≫ c)) (Spec.map_comp a c).symm A

variable {R S R' S' R'' S'' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)

include w v in
/-- Two affine refinement squares have a commutative composite square. -/
theorem composite_square : φ ≫ (b ≫ d) = (a ≫ c) ≫ χ := by
  rw [← Category.assoc, w, Category.assoc, v, Category.assoc]

/-- The affine square comparisons compose after the actual base and cover charts. -/
@[reassoc]
theorem squareIso_composition (A : (Spec R).Modules) :
    (pullback (Spec.map χ)).map (compositionChart a c A).hom ≫
        (squareIso φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v)).hom.app A =
      (squareIso ψ χ c d v).hom.app ((pullback (Spec.map a)).obj A) ≫
        (pullback (Spec.map d)).map ((squareIso φ ψ a b w).hom.app A) ≫
        (compositionChart b d ((pullback (Spec.map φ)).obj A)).hom :=
  SchemePullbackSquare.squareIso_composition_of_eq (Spec.map φ) (Spec.map ψ)
    (Spec.map χ) (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d)
    (spec_square φ ψ a b w) (spec_square ψ χ c d v)
    (Spec.map (a ≫ c)) (Spec.map (b ≫ d)) (Spec.map_comp a c).symm
    (Spec.map_comp b d).symm
    (spec_square φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v)) A
    (squareIso φ ψ a b w) (squareIso ψ χ c d v)
    (squareIso φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v))
    (squareIso_eq_scheme φ ψ a b w) (squareIso_eq_scheme ψ χ c d v)
    (squareIso_eq_scheme φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v))
    (compositionChart a c A) (compositionChart b d ((pullback (Spec.map φ)).obj A))
    rfl rfl

/-- Successive affine reconstruction agrees with reconstruction of the composite square. -/
@[reassoc]
theorem reconstruction_composition {A : (Spec R).Modules} {M : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ M) :
    (reconstruction ψ χ c d v (reconstruction φ ψ a b w e)).hom ≫
        (compositionChart b d M).hom =
      (pullback (Spec.map χ)).map (compositionChart a c A).hom ≫
        (reconstruction φ χ (a ≫ c) (b ≫ d)
          (composite_square φ ψ χ a b c d w v) e).hom :=
  SchemePullbackSquare.reconstruction_composition_of_eq (Spec.map φ) (Spec.map ψ)
    (Spec.map χ) (Spec.map a) (Spec.map b) (Spec.map c) (Spec.map d)
    (spec_square φ ψ a b w) (spec_square ψ χ c d v)
    (Spec.map (a ≫ c)) (Spec.map (b ≫ d)) (Spec.map_comp a c).symm
    (Spec.map_comp b d).symm
    (spec_square φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v)) e
    (reconstruction φ ψ a b w e)
    (reconstruction ψ χ c d v (reconstruction φ ψ a b w e))
    (reconstruction φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) e)
    (reconstruction_eq_chart φ ψ a b w e)
    (reconstruction_eq_chart ψ χ c d v (reconstruction φ ψ a b w e))
    (reconstruction_eq_chart φ χ (a ≫ c) (b ≫ d)
      (composite_square φ ψ χ a b c d w v) e)
    (compositionChart a c A) (compositionChart b d M) rfl rfl

end FLT.Mazur.AffineRefinementPullback
