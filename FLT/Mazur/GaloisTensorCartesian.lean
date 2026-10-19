/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.GaloisTensorSchemeCover
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The original tensor overlap as a Cartesian coefficient square

The two coefficient projections make the original tensor spectrum a pullback.
Galois evaluations retain the identity and automorphism on its two projections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.GaloisTensorPrime

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- First coefficient projection of the original tensor spectrum. -/
def tensorFst : Spec (.of (L ⊗[K] L)) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- Second coefficient projection of the original tensor spectrum. -/
def tensorSnd : Spec (.of (L ⊗[K] L)) ⟶ Spec (.of L) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)

/-- These are the actual two projections of the coefficient kernel pair. -/
theorem tensor_isPullback : IsPullback (tensorFst (K := K) (L := L)) tensorSnd
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct K L L)

/-- Evaluation fixes the first coefficient literally. -/
@[reassoc] theorem evaluationSpec_fst (g : L ≃ₐ[K] L) :
    evaluationSpec g ≫ tensorFst = 𝟙 _ := by
  rw [evaluationSpec, tensorFst, ← Spec.map_comp]
  have h : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
      CommRingCat.ofHom (evaluation g).toRingHom = 𝟙 (CommRingCat.of L) := by
    ext x
    change x * g 1 = x
    rw [map_one, mul_one]
  rw [h, Spec.map_id]

/-- Evaluation applies the original automorphism to the second coefficient. -/
@[reassoc] theorem evaluationSpec_snd (g : L ≃ₐ[K] L) :
    evaluationSpec g ≫ tensorSnd = Spec.map (CommRingCat.ofHom g.toRingHom) := by
  rw [evaluationSpec, tensorSnd, ← Spec.map_comp]
  congr 1
  ext x
  exact one_mul (g x)

end FLT.Mazur.GaloisTensorPrime
