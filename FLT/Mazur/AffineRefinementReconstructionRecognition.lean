/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRefinementComposition

/-!
# Reconstruction composition with a named intermediate sheaf

Transport the composition square through an equality identifying the intermediate
sheaf. The transport takes place before substituting concrete descended sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' R'' S'' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)

/-- Recognize reconstruction composition with an explicitly identified intermediate object. -/
theorem reconstruction_composition_named {A : (Spec R).Modules} {M : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ M)
    (A' : (Spec R').Modules) (hA : A' = (pullback (Spec.map a)).obj A)
    (E : (pullback (Spec.map ψ)).obj A' ≅ (pullback (Spec.map b)).obj M)
    (hE : HEq E (reconstruction φ ψ a b w e))
    (B : (pullback (Spec.map c)).obj A' ≅ (pullback (Spec.map (a ≫ c))).obj A)
    (hB : HEq B (compositionChart a c A)) :
    (reconstruction ψ χ c d v E).hom ≫ (compositionChart b d M).hom =
      (pullback (Spec.map χ)).map B.hom ≫
        (reconstruction φ χ (a ≫ c) (b ≫ d)
          (composite_square φ ψ χ a b c d w v) e).hom := by
  subst A'
  cases eq_of_heq hE
  cases eq_of_heq hB
  exact reconstruction_composition φ ψ χ a b c d w v e

end FLT.Mazur.AffineRefinementPullback
