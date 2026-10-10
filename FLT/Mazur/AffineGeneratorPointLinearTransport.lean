/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSectionLinePoint
public import FLT.Mazur.FiniteFreeSectionLineTransport

/-!
# Actual affine generator points under dual projective transitions

The affine point of a vector with a unit coordinate is its original
homogeneous point. An ambient finite free change of coordinates therefore
transports this actual affine point through the dual projective isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.ProjectiveSpace
open NormalizedSectionLine FiniteFreeContragredient
variable {X : Scheme.{u}} [IsAffine X] {ι κ : Type u}

/-- The actual affine image-line point is the original homogeneous vector point. -/
lemma affineGeneratorPoint_eq_unitChartPoint {R : Type u} [CommRing R]
    (φ : R →+* Γ(X, ⊤)) (v : ι → Γ(X, ⊤)) (i : ι) (a : Γ(X, ⊤)ˣ) (hi : v i = a) :
    affineGeneratorPoint φ v i a hi = X.isoSpec.hom ≫ unitChartPoint R ι φ v i a hi := by
  unfold affineGeneratorPoint affineSectionLinePoint
  rw [sectionLinePoint_eq_unitChartPoint]
  apply congrArg (X.isoSpec.hom ≫ ·)
  have h := unitChartPoint_scale R ι φ v i a a⁻¹ hi
  simpa only [unitCoordinateLine_generator, inv_mul_cancel, Pi.smul_def, smul_eq_mul]
    using h

/-- Original finite free section transport induces the genuine dual affine projective action. -/
lemma affineGeneratorPoint_linearTransport [Finite ι] [Finite κ]
    (e : (ι →₀ Γ(X, ⊤)) ≃ₗ[Γ(X, ⊤)] (κ →₀ Γ(X, ⊤)))
    (v : ι → Γ(X, ⊤)) (i : ι) (j : κ) (a b : Γ(X, ⊤)ˣ)
    (hi : v i = a) (hj : functionCoordinates e v j = b) :
    affineGeneratorPoint (.id _) v i a hi ≫ (linearIso (map e)).hom =
      affineGeneratorPoint (.id _) (functionCoordinates e v) j b hj := by
  rw [affineGeneratorPoint_eq_unitChartPoint, affineGeneratorPoint_eq_unitChartPoint,
    Category.assoc]
  apply congrArg (X.isoSpec.hom ≫ ·)
  let w := (Finsupp.linearEquivFunOnFinite Γ(X, ⊤) Γ(X, ⊤) ι).symm v
  exact unitChartPoint_transport e w i j a b hi hj

end FLT.Mazur.ProjectiveSpace
