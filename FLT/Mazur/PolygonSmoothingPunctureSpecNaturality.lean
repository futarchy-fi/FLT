/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureSpecCalculus
public import FLT.Mazur.PolygonSmoothingPunctureNaturality

/-!
# Coefficient squares for the full Laurent spectrum calculus

Full Laurent substitutions compose across coefficient maps. Their geometric
squares reflect back to the entire algebra, not merely the coordinate's
reduced image.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
open PolygonScalingNaturality LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- Both original puncture arrows preserve the explicit coefficient homomorphism. -/
@[reassoc] theorem punctureOpen_ringMap (t : R) (s : S) (hs : f t = s) (b : Bool) :
    punctureOpen s b ≫ Spec.map (CommRingCat.ofHom (ringMap f t s hs)) =
      Spec.map (CommRingCat.ofHom (coeffMap f)) ≫ punctureOpen t b := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (ringMap_punctureLaurent f t s hs b))

/-- A geometric quotient square reflects the full coefficient square on Laurent functions. -/
theorem punctureSpecIso_naturality_iff
    (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) (b : S[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹]) :
    (punctureSpecIso b).hom ≫ Spec.map (CommRingCat.ofHom (coeffMap f)) =
        Spec.map (CommRingCat.ofHom (coeffMap f)) ≫ (punctureSpecIso a).hom ↔
      (coeffMap f).comp a.toAlgHom.toRingHom =
        b.toAlgHom.toRingHom.comp (coeffMap f) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ↔ _
  rw [← Spec.map_comp, ← Spec.map_comp]
  constructor
  · intro h
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h)).symm
  · intro h
    exact congrArg Spec.map (CommRingCat.hom_ext h.symm)

/-- Full coefficient squares are stable under composition in algebra order. -/
theorem punctureEquiv_trans_naturality
    (a c : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) (b d : S[T;T⁻¹] ≃ₐ[S] S[T;T⁻¹])
    (ha : (coeffMap f).comp a.toAlgHom.toRingHom =
      b.toAlgHom.toRingHom.comp (coeffMap f))
    (hc : (coeffMap f).comp c.toAlgHom.toRingHom =
      d.toAlgHom.toRingHom.comp (coeffMap f)) :
    (coeffMap f).comp (a.trans c).toAlgHom.toRingHom =
      (b.trans d).toAlgHom.toRingHom.comp (coeffMap f) := by
  apply RingHom.ext
  intro z
  exact (DFunLike.congr_fun hc (a z)).trans (congrArg d (DFunLike.congr_fun ha z))

/-- Coefficient change preserves the original inverse Laurent coordinate. -/
theorem punctureEquiv_invert_naturality :
    (coeffMap f).comp invert.toAlgHom.toRingHom =
      invert.toAlgHom.toRingHom.comp (coeffMap f) := by
  apply ringHom_ext <;> simp

end FLT.Mazur.PolygonSmoothing
