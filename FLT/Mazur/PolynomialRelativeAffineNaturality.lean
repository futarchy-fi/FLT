/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIdealCoordinates
public import FLT.Mazur.PolynomialRelativeAffineChart

/-!
# Naturality of polynomial charts and full coordinate ideals

A morphism between affine base tests induces the ordinary coefficient map
on their polynomial spectra. Restricting any supplied scheme ideal therefore
extends its actual coordinate ideal by this polynomial coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R]
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (a : Spec (.of S) ⟶ X)
variable (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R S)))
variable (b : Spec (.of T) ⟶ X)
variable (hb : b ≫ s = Spec.map (CommRingCat.ofHom (algebraMap R T)))
variable (f : S →ₐ[R] T) (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ a = b)

include hf

/-- Polynomial affine charts commute with the actual algebra map of affine base tests. -/
theorem polynomialRelativeAffineChart_natural :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map f.toRingHom)) ≫
        polynomialRelativeAffineChart R I s S a ha =
      polynomialRelativeAffineChart R I s T b hb := by
  apply pullback.hom_ext
  · rw [Category.assoc, polynomialRelativeAffineChart_fst,
      polynomialRelativeAffineChart_fst, ← Category.assoc, ← Spec.map_comp]
    have h : CommRingCat.ofHom (MvPolynomial.C (R := S) (σ := I)) ≫
        CommRingCat.ofHom (MvPolynomial.map f.toRingHom) =
      CommRingCat.ofHom f.toRingHom ≫
        CommRingCat.ofHom (MvPolynomial.C (R := T) (σ := I)) := by
      apply CommRingCat.hom_ext
      exact MvPolynomial.map_comp_C f.toRingHom
    rw [h, Spec.map_comp, Category.assoc, hf]
  · rw [Category.assoc, polynomialRelativeAffineChart_snd,
      polynomialRelativeAffineChart_snd, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change (MvPolynomial.map f.toRingHom).comp (MvPolynomial.map (algebraMap R S)) = _
    ext x <;> simp

/-- The full coordinate ideal of a restricted scheme family commutes with affine base change. -/
theorem polynomialRelativeCoordinateIdeal_natural
    (J : (polynomialRelativeAmbient R I s).IdealSheafData) :
    coordinateIdeal (.of (MvPolynomial I T))
        (J.comap (polynomialRelativeAffineChart R I s T b hb)) =
      (coordinateIdeal (.of (MvPolynomial I S))
        (J.comap (polynomialRelativeAffineChart R I s S a ha))).map
          (MvPolynomial.map f.toRingHom) := by
  rw [← polynomialRelativeAffineChart_natural R I s S T a ha b hb f hf,
    Scheme.IdealSheafData.comap_comp, coordinateIdeal_comap_specMap]
  rfl

end FLT.Mazur.HilbertChart
