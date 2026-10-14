/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentUnitScaledCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Coefficient-preserving isomorphisms for scaled Laurent coordinates

The substitutions used in the actual component charts are isomorphisms
of schemes over the original coefficient spectrum. In particular they
preserve open immersions and do not replace a chart by an abstract point set.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonScaledReciprocal
universe u
variable {R : Type u} [CommRing R]

/-- Consecutive scaling substitutions multiply the original coefficient units. -/
theorem scaling_comp (a b : Rˣ) :
    (scaling a).comp (scaling b) = scaling (a * b) := by
  apply AlgHom.coe_ringHom_injective
  exact (PolygonScalingNaturality.laurent_mul a b).symm

/-- Scaling by one is the identity on the entire Laurent algebra. -/
@[simp] theorem scaling_one : scaling (1 : Rˣ) = AlgHom.id R _ := by
  apply AlgHom.coe_ringHom_injective
  exact PolygonScalingNaturality.laurent_one

/-- Scaling is an algebra automorphism with inverse given by the inverse coefficient. -/
def scalingEquiv (a : Rˣ) : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom (scaling a) (scaling a⁻¹)
    (by rw [scaling_comp, mul_inv_cancel, scaling_one])
    (by rw [scaling_comp, inv_mul_cancel, scaling_one])

/-- The underlying scaling spectrum map is an isomorphism. -/
instance scaling_spec_isIso (a : Rˣ) :
    IsIso (Spec.map (CommRingCat.ofHom (scaling a).toRingHom)) := by
  change IsIso (Scheme.Spec.mapIso
    (scalingEquiv a).toRingEquiv.toCommRingCatIso.op).hom
  infer_instance

/-- The underlying reciprocal spectrum map is an isomorphism. -/
instance reciprocal_spec_isIso (a : Rˣ) :
    IsIso (Spec.map (CommRingCat.ofHom (reciprocal a).toRingHom)) := by
  change IsIso (Scheme.Spec.mapIso
    (equiv a).toRingEquiv.toCommRingCatIso.op).hom
  infer_instance

/-- Scaling keeps the original map from coefficients on the whole spectrum. -/
@[reassoc] theorem scaling_spec_structure (a : Rˣ) :
    Spec.map (CommRingCat.ofHom (scaling a).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (scaling a).comp_algebraMap

/-- Scaled inversion keeps the original map from coefficients on the whole spectrum. -/
@[reassoc] theorem reciprocal_spec_structure (a : Rˣ) :
    Spec.map (CommRingCat.ofHom (reciprocal a).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (algebraMap R R[T;T⁻¹])) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (reciprocal a).comp_algebraMap

end FLT.Mazur.PolygonScaledReciprocal
