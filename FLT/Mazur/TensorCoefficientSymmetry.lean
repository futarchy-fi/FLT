/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChart
public import FLT.Mazur.CartesianCoefficientSymmetry

/-!
# Coefficient symmetry in the original tensor charts

The automorphism changes the first tensor factor and fixes every original
chart function. Its spectrum realizes the actual Cartesian coefficient
operation, preserving both projections of the original affine chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorCoefficientSymmetry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] (e : S ≃ₐ[R] S)

/-- The exact semilinear action on the coefficient tensor factor. -/
def equiv : S ⊗[R] A ≃ₐ[R] S ⊗[R] A :=
  Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[R] A)

/-- Every pure tensor retains its original chart coordinate. -/
@[simp] theorem equiv_tmul (s : S) (a : A) :
    equiv e (s ⊗ₜ[R] a) = e s ⊗ₜ[R] a := rfl

/-- The coefficient spectrum operation. -/
def coefficient : Spec (.of S) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom e.toRingHom)

/-- The coefficient operation lies over the original base ring. -/
@[reassoc] theorem coefficient_structure :
    coefficient e ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [coefficient, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact e.toAlgHom.comp_algebraMap

/-- The semilinear automorphism of the full tensor spectrum. -/
def spectrum : Spec (.of (S ⊗[R] A)) ⟶ Spec (.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (equiv (A := A) e).toRingHom)

/-- The original affine chart projection is fixed exactly. -/
@[reassoc] theorem spectrum_projection :
    spectrum (A := A) e ≫ TensorOpenChart.projection = TensorOpenChart.projection := by
  rw [spectrum, TensorOpenChart.projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  change equiv e (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
  simp only [equiv_tmul, map_one]

/-- The full coefficient projection transforms by the specified algebra automorphism. -/
@[reassoc] theorem spectrum_structure :
    spectrum (A := A) e ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ≫ coefficient e := by
  simp only [spectrum, coefficient, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- The original affine tensor chart intertwines the genuine Cartesian coefficient symmetry. -/
theorem chart_symmetry {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (i : Spec (.of A) ⟶ X)
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    spectrum e ≫ TensorOpenChart.chart f i hi =
      TensorOpenChart.chart f i hi ≫ CartesianCoefficientSymmetry.map
        (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) f).flip
        (coefficient e) (coefficient_structure e) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, TensorOpenChart.chart_fst,
      CartesianCoefficientSymmetry.map_coefficient]
    rw [← Category.assoc, TensorOpenChart.chart_fst, spectrum_structure]
  · simp only [Category.assoc, TensorOpenChart.chart_snd,
      CartesianCoefficientSymmetry.map_original, spectrum_projection_assoc]

end FLT.Mazur.TensorCoefficientSymmetry
