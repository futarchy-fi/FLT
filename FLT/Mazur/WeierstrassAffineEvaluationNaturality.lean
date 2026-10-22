/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineVariableChangeSections
public import FLT.Mazur.WeierstrassChartCoefficientRingMap

/-!
# Scheme naturality from the complete affine evaluation square

An equality of evaluated ring maps identifies the actual scheme maps, even
when the schemes on which the functions are evaluated are not affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
/-- A triple composite of coefficient evaluations gives the corresponding square of spectra. -/
theorem coordinateEvaluation_square {X Y : Scheme} (π : X ⟶ Y)
    {A B D : CommRingCat} (c : A ⟶ B) (d : B ⟶ D)
    (p : D ⟶ Γ(X, ⊤)) (q : A ⟶ Γ(Y, ⊤))
    (h : c ≫ d ≫ p = q ≫ π.appTop) :
    (X.toSpecΓ ≫ Spec.map p) ≫ Spec.map d ≫ Spec.map c =
      π ≫ Y.toSpecΓ ≫ Spec.map q := by
  rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc c, h, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]

/-- Ring-valued evaluations give the same square without exposing coordinate-ring definitions. -/
theorem coordinateRingEvaluation_square {X Y : Scheme} (π : X ⟶ Y)
    {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
    (c : A →+* B) (d : B →+* D) (p : D →+* Γ(X, ⊤)) (q : A →+* Γ(Y, ⊤))
    (h : p.comp (d.comp c) = π.appTop.hom.comp q) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom p)) ≫
      Spec.map (CommRingCat.ofHom d) ≫ Spec.map (CommRingCat.ofHom c) =
        π ≫ Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q) :=
  coordinateEvaluation_square π (CommRingCat.ofHom c) (CommRingCat.ofHom d)
    (CommRingCat.ofHom p) (CommRingCat.ofHom q) (CommRingCat.hom_ext h)

/-- The affine scheme comparison retains its original coordinate-ring homomorphism. -/
theorem affineVariableChangeIso_hom_ringMap {R : Type} [CommRing R]
    (W V : WeierstrassCurve R) (C : VariableChange R) (h : C • W = V) :
    (affineVariableChangeIso W V C h).hom =
      Spec.map (CommRingCat.ofHom (affineVariableChangeMap W V C h).toRingHom) := rfl

attribute [local irreducible] affineVariableChangeIso affineVariableChangeMap
  chartCoefficientRingMap

variable {R S : Type} [CommRing R] [CommRing S]
  {X Y : Scheme} (π : X ⟶ Y) (f : R →+* S)
  (W : WeierstrassCurve R) (V : WeierstrassCurve S)
  (C : VariableChange S) (hC : C • W.map f = V)
  (p : Coordinate V 2 →+* Γ(X, ⊤)) (q : Coordinate W 2 →+* Γ(Y, ⊤))

/-- A commuting evaluation square gives the full affine variable and coefficient change square. -/
theorem affineEvaluation_coefficient_square
    (h : p.comp ((affineVariableChangeMap (W.map f) V C hC).toRingHom.comp
      (chartCoefficientRingMap f W 2)) = π.appTop.hom.comp q) :
    (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom p)) ≫
      (affineVariableChangeIso (W.map f) V C hC).hom ≫
        Spec.map (CommRingCat.ofHom (chartCoefficientRingMap f W 2)) =
      π ≫ Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom q) := by
  rw [affineVariableChangeIso_hom_ringMap]
  exact coordinateRingEvaluation_square π (chartCoefficientRingMap f W 2)
    (affineVariableChangeMap (W.map f) V C hC).toRingHom p q h

end FLT.Mazur.WeierstrassIntegralChart
