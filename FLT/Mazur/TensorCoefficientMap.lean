/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChart

/-!
# Changing coefficients on the full tensor chart

An arbitrary coefficient algebra map fixes the original chart functions.
Both projections identify its spectrum with the actual base-change map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorCoefficientMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
  [Algebra R S] [Algebra R T] [Algebra R A] (f : S →ₐ[R] T)

/-- Change only the coefficient factor of the original tensor algebra. -/
def algebra : S ⊗[R] A →ₐ[R] T ⊗[R] A :=
  Algebra.TensorProduct.map f (AlgHom.id R A)

/-- The original affine function is unchanged on pure tensors. -/
theorem algebra_tmul (s : S) (a : A) :
    algebra f (s ⊗ₜ[R] a) = f s ⊗ₜ[R] a := rfl

/-- The actual contravariant map of full tensor spectra. -/
def spectrum : Spec (.of (T ⊗[R] A)) ⟶ Spec (.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (algebra (A := A) f).toRingHom)

/-- Every original affine function survives coefficient restriction. -/
@[reassoc] theorem spectrum_projection :
    spectrum (A := A) f ≫ TensorOpenChart.projection = TensorOpenChart.projection := by
  rw [spectrum, TensorOpenChart.projection, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  change algebra f (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
  simp only [algebra_tmul, map_one]

/-- The coefficient projection uses precisely the given algebra map. -/
@[reassoc] theorem spectrum_structure :
    spectrum (A := A) f ≫ Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) =
      Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] A))) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) := by
  simp only [spectrum, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- The two original projections determine the entire coefficient square. -/
theorem square_of_projections {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (i : Spec (.of A) ⟶ X)
    (cS : Spec (.of (S ⊗[R] A)) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (cT : Spec (.of (T ⊗[R] A)) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (r : pullback p (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⟶
      pullback p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hS : cS ≫ pullback.fst _ _ = TensorOpenChart.projection ≫ i)
    (hT : cT ≫ pullback.fst _ _ = TensorOpenChart.projection ≫ i)
    (bS : cS ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))))
    (bT : cT ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] A))))
    (hr : r ≫ pullback.fst _ _ = pullback.fst _ _)
    (br : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      Spec.map (CommRingCat.ofHom f.toRingHom)) :
    spectrum f ≫ cS = cT ≫ r := by
  apply pullback.hom_ext
  · simp only [Category.assoc, hS, hT, hr, spectrum_projection_assoc]
  · rw [Category.assoc, bS, Category.assoc, br, ← Category.assoc, bT, spectrum_structure]

end FLT.Mazur.TensorCoefficientMap
