/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartMap
public import FLT.Mazur.GrassmannianAmbientNormalizedQuotient
public import FLT.Mazur.GrassmannianNormalizedBaseChange

/-!
# Coefficient naturality of original ambient coordinate points

Applying a coefficient homomorphism entrywise to the matrix produces precisely
the actual Grassmannian functor image, including its full relation submodule.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B M κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}

/-- Scalar extension of normalized ambient evaluation applies the map to every matrix entry. -/
theorem ambientNormalizedQuotient_baseChange [Algebra A B] [IsScalarTower R A B]
    (i : AmbientChartIndex R M κ d) (c : Matrix (Fin d) κ A) :
    let _ := Classical.decEq κ
    normalizedQuotientBaseChange (B := B) (ambientNormalizedQuotient i (Matrix.toLin' c)) =
      ambientNormalizedQuotient i (Matrix.toLin' (c.map (algebraMap A B))) := by
  classical
  dsimp only
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    rw [normalizedQuotientBaseChange_tmul, ambientNormalizedQuotient_tmul,
      ambientNormalizedQuotient_tmul]
    ext j
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_add, map_sum, map_mul,
      ← IsScalarTower.algebraMap_apply, Finset.sum_mul, add_mul, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Matrix specialization gives the original functor map on full ambient quotient points. -/
theorem ambientPointOfCoordinates_map (f : A →ₐ[R] B)
    (i : AmbientChartIndex R M κ d) (c : Matrix (Fin d) κ A) :
    let _ := Classical.decEq κ
    Module.Grassmannian.map f (ambientPointOfCoordinates i (Matrix.toLin' c)).val =
      (ambientPointOfCoordinates i (Matrix.toLin' (c.map f))).val := by
  classical
  dsimp only
  let _ : Algebra A B := f.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.algebraMap_eq R A B)
  have hf : f = IsScalarTower.toAlgHom R A B := by ext; rfl
  apply Module.Grassmannian.ext
  rw [hf, grassmannian_map_normalized_kernel _ _ (ambientNormalizedQuotientEquiv i _)
    (ambientNormalizedQuotientEquiv_mkQ i _), ambientNormalizedQuotient_baseChange]
  exact ambientNormalizedQuotient_kernel i _

/-- The same naturality holds in the chart subtype, retaining the selected-basis witness. -/
theorem ambientChartMap_ofCoordinates (f : A →ₐ[R] B)
    (i : AmbientChartIndex R M κ d) (c : Matrix (Fin d) κ A) :
    let _ := Classical.decEq κ
    ambientChartMap f i (ambientPointOfCoordinates i (Matrix.toLin' c)) =
      ambientPointOfCoordinates i (Matrix.toLin' (c.map f)) := by
  classical
  apply Subtype.ext
  exact ambientPointOfCoordinates_map f i c

end FLT.Mazur.GrassmannianChart
