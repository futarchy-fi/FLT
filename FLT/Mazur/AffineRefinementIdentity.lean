/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineRefinementPullback
public import FLT.Mazur.SchemeRefinementReconstruction

/-!
# Identity charts for affine refinement

Identity ring maps give objectwise unit charts. Identity refinement of a
reconstruction respects these actual charts on the base and cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem identity_chart_of_eq {X Y : Scheme.{u}} (p : Y ⟶ X)
    (a : X ⟶ X) (b : Y ⟶ Y) (ha : a = 𝟙 X) (hb : b = 𝟙 Y)
    (w : p ≫ a = b ≫ p) {A : X.Modules} {M : Y.Modules}
    (e : (pullback p).obj A ≅ M)
    (E : (pullback p).obj ((pullback a).obj A) ≅ (pullback b).obj M)
    (hE : E = SchemePullbackSquare.reconstructionChart p p a b w e) :
    E.hom ≫ (SchemePullbackSquare.identityChart b hb M).hom =
      (pullback p).map (SchemePullbackSquare.identityChart a ha A).hom ≫ e.hom := by
  rw [hE]
  exact SchemePullbackSquare.reconstructionChart_identity p a b ha hb w e

/-- The affine reconstruction has the explicit scheme reconstruction chart. -/
theorem reconstruction_eq_chart {R S R' S' : CommRingCat.{u}}
    (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
    (w : φ ≫ b = a ≫ ψ) {A : (Spec R).Modules} {M : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj A ≅ M) :
    reconstruction φ ψ a b w e =
      SchemePullbackSquare.reconstructionChart (Spec.map φ) (Spec.map ψ)
        (Spec.map a) (Spec.map b) (spec_square φ ψ a b w) e := rfl

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {A : (Spec R).Modules} {M : (Spec S).Modules}

/-- Affine refinements inducing identity scheme maps respect the unit charts. -/
theorem reconstruction_identity (a : R ⟶ R) (b : S ⟶ S)
    (ha : Spec.map a = 𝟙 (Spec R)) (hb : Spec.map b = 𝟙 (Spec S))
    (w : φ ≫ b = a ≫ φ) (e : (pullback (Spec.map φ)).obj A ≅ M) :
    (reconstruction φ φ a b w e).hom ≫
        (SchemePullbackSquare.identityChart (Spec.map b) hb M).hom =
      (pullback (Spec.map φ)).map
        (SchemePullbackSquare.identityChart (Spec.map a) ha A).hom ≫ e.hom :=
  identity_chart_of_eq (Spec.map φ) (Spec.map a) (Spec.map b) ha hb
    (spec_square φ φ a b w) e (reconstruction φ φ a b w e)
    (reconstruction_eq_chart φ φ a b w e)


end FLT.Mazur.AffineRefinementPullback
