/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjUnitChart
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Structural maps for Proj of a graded algebra

The degree-zero structural algebra defines a morphism to the scalar spectrum.
Its composite with any unit-coordinate chart is the expected map on scalars.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
universe u
namespace FLT.Mazur.GradedProjStructuralMap
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Proj of a graded algebra maps to the spectrum of its structural scalars. -/
def toSpecBase : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

/-- The scalar map to a homogeneous localization factors through degree zero. -/
def scalarToAway (f : A) : R →+* Away 𝒜 f :=
  (fromZeroRingHom 𝒜 _).comp (algebraMap R (𝒜 0))

/-- The structural map on a standard affine Proj chart. -/
@[reassoc]
lemma awayι_toSpecBase {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι 𝒜 f hf hd ≫ toSpecBase 𝒜 =
      Spec.map (CommRingCat.ofHom (scalarToAway 𝒜 f)) := by
  rw [toSpecBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- Unit-coordinate evaluation sends a degree-zero fraction to its numerator. -/
lemma evaluation_fromZero {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤))
    (f : A) (hf : IsUnit (φ f)) (a : 𝒜 0) :
    GradedProjUnitChart.evaluation 𝒜 φ f hf (fromZeroRingHom 𝒜 _ a) = φ a := by
  have h := GradedProjUnitChart.evaluation_mk_mul 𝒜 φ f hf ⟨0, a, 1, one_mem _⟩
  change GradedProjUnitChart.evaluation 𝒜 φ f hf (fromZeroRingHom 𝒜 _ a) * φ 1 = φ a at h
  simpa only [map_one, mul_one] using h

/-- Evaluation on scalar fractions is the original structural scalar action. -/
lemma evaluation_scalarToAway {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤))
    (f : A) (hf : IsUnit (φ f)) :
    (GradedProjUnitChart.evaluation 𝒜 φ f hf).comp (scalarToAway 𝒜 f) =
      φ.comp (algebraMap R A) := by
  ext r
  exact evaluation_fromZero 𝒜 φ f hf (algebraMap R (𝒜 0) r)

/-- A unit-coordinate chart commutes with the structural morphism. -/
@[reassoc]
lemma unitChart_toSpecBase {X : Scheme.{u}} (φ : A →+* Γ(X, ⊤))
    (f : A) (hf : IsUnit (φ f)) {d : ℕ} (hdeg : f ∈ 𝒜 d) (hd : 0 < d) :
    GradedProjUnitChart.toProj 𝒜 φ f hf hdeg hd ≫ toSpecBase 𝒜 =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R A))) := by
  rw [GradedProjUnitChart.toProj, Category.assoc, awayι_toSpecBase]
  simp only [GradedProjUnitChart.toAffine, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, evaluation_scalarToAway]

end FLT.Mazur.GradedProjStructuralMap
