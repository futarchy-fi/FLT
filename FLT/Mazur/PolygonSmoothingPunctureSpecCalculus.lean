/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingPunctureGeometry

/-!
# Faithful contravariant calculus for full Laurent equivalences

These identities preserve composition order when passing between full
Laurent algebra automorphisms and the actual edge scheme isomorphisms.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency false

/-- Spectrum reverses the order of full Laurent substitutions. -/
theorem punctureSpecIso_trans (a b : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) :
    punctureSpecIso (a.trans b) = punctureSpecIso b ≪≫ punctureSpecIso a := by
  apply Iso.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- Spectrum preserves inversion of the full substitution. -/
theorem punctureSpecIso_symm (a : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) :
    punctureSpecIso a.symm = (punctureSpecIso a).symm := rfl

/-- The identity algebra substitution gives the identity geometric edge. -/
theorem punctureSpecIso_refl :
    punctureSpecIso (AlgEquiv.refl : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]) = Iso.refl _ := by
  apply Iso.ext
  exact Spec.map_id _

/-- Equality of the geometric edges detects equality of the entire algebra substitutions. -/
theorem punctureSpecIso_injective :
    Function.Injective (punctureSpecIso (R := R)) := by
  intro a b h
  have hh := Spec.map_injective (congrArg Iso.hom h)
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun f ↦ f.hom z) hh

/-- Original edge inversion is the spectrum of Laurent inversion. -/
theorem punctureSpecIso_invert :
    punctureSpecIso (LaurentPolynomial.invert (R := R)) = edgeInversion R := rfl

end FLT.Mazur.PolygonSmoothing
