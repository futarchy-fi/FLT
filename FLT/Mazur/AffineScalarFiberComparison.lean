/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Scalar coordinates and actual affine fibers

A finite scheme over an affine base is the spectrum of its global sections
with the original scalar map. Its field fibers have exactly the points of
the corresponding tensor-product spectra, including all scheme structure.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.AffineScalarFiberComparison

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The original affine structure morphism determines this scalar map. -/
def scalarMap : R →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom

/-- Passing to scalar coordinates retains the original structure morphism. -/
theorem factorization [IsAffine X] :
    f = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (scalarMap f)) := by
  simp only [scalarMap, CommRingCat.ofHom_hom, Spec.map_comp]
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp [Scheme.isoSpec_Spec_hom]

/-- A finite scheme has a finite global section algebra with its original scalar map. -/
theorem scalarMap_finite [IsFinite f] : (scalarMap f).Finite :=
  f.finite_appTop.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2)

/-- Formal unramifiedness carries over to the actual global section algebra. -/
theorem scalarMap_formallyUnramified [IsAffine X] [FormallyUnramified f] :
    (scalarMap f).FormallyUnramified := by
  apply (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)
    (φ := CommRingCat.ofHom (scalarMap f))).mp
  have he : Spec.map (CommRingCat.ofHom (scalarMap f)) = X.isoSpec.inv ≫ f := by
    conv_rhs => rw [factorization f]
    simp only [Iso.inv_hom_id_assoc]
  rw [he]
  exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

/-- Flatness of the scalar algebra gives flatness of the original scheme morphism. -/
theorem flat_of_scalarMap [IsAffine X] (hf : (scalarMap f).Flat) : Flat f := by
  have : Flat (Spec.map (CommRingCat.ofHom (scalarMap f))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hf
  rw [factorization f]
  infer_instance

/-- Tensor-product spectra count the actual geometric fibers of the original morphism. -/
theorem fiber_card_tensor [IsAffine X] (K : Type u) [Field K] [Algebra R K] :
    let _ := (scalarMap f).toAlgebra
    Nat.card (Spec (.of (K ⊗[R] Γ(X, ⊤)))) =
      Nat.card (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme.{u}) := by
  let _ := (scalarMap f).toAlgebra
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let h := Spec.map (CommRingCat.ofHom (scalarMap f))
  let e : pullback f g ≅ pullback h g :=
    asIso (pullback.map f g h g X.isoSpec.hom (𝟙 _) (𝟙 _)
      (by simpa using factorization f) (by simp))
  let d := e ≪≫ pullbackSymmetry h g ≪≫ pullbackSpecIso R K Γ(X, ⊤)
  exact (Nat.card_congr d.hom.homeomorph.toEquiv).symm

end FLT.Mazur.AffineScalarFiberComparison
