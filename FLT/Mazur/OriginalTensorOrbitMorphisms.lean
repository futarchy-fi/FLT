/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTranscendentalAffineOpenOrbit
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Whole scheme morphisms of original algebraic point orbits

The unchanged extended affine evaluations define rational scheme morphisms.
Their projections retain the original algebraic point and both coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
set_option backward.isDefEq.respectTransparency false
variable {k L K A : Type} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [CommRing A] [Algebra k A]

/-- The whole original algebraic point, with its original coordinate map. -/
def originalPointMorphism (q : A →ₐ[k] L) : Spec (.of L) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom q.toRingHom)

/-- The whole larger-field rational point of the tensor spectrum. -/
def originalExtendedMorphism (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L) :
    Spec (.of K) ⟶ Spec (.of (K ⊗[k] A)) :=
  Spec.map (CommRingCat.ofHom (originalEvaluation (K := K) q σ).toRingHom)

/-- The larger-field point is rational over the unchanged coefficient field. -/
@[reassoc]
theorem originalExtendedMorphism_base (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L) :
    originalExtendedMorphism (K := K) q σ ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A))) = 𝟙 _ := by
  rw [originalExtendedMorphism, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of K) using 1
  congr 1
  ext z
  exact (originalEvaluation (K := K) q σ).commutes z

/-- Projection keeps the entire conjugated original point, not just its support. -/
@[reassoc]
theorem originalExtendedMorphism_original (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L) :
    originalExtendedMorphism (K := K) q σ ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ originalPointMorphism q := by
  simp only [originalExtendedMorphism, originalPointMorphism, ← Spec.map_comp]
  congr 1
  ext a
  exact one_mul _

/-- The support is exactly the prime used by the affine orbit avoidance theorem. -/
theorem originalExtendedMorphism_apply (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L)
    (x : Spec (.of K)) :
    originalExtendedMorphism (K := K) q σ x = originalExtendedPoint (K := K) q σ := by
  apply PrimeSpectrum.ext
  change Ideal.comap _ x.asIdeal = RingHom.ker _
  rw [Subsingleton.elim x (⊥ : PrimeSpectrum K)]
  rfl

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
