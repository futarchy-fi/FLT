/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTangentConjugation
public import FLT.Mazur.WeierstrassCoefficientShearSpecialization

/-!
# Actual residue-tangent conjugation and whole-model specialization

The residue-root equation gluing carries the original quadratic involution.
Its full specialization into the integral tangent model is equivariant on
both coefficient and integral-model projections.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "V" => W.map (residue R)
local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "rQ" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "sQ" => coefficientShearGluedStructure hπ data Q rQ j hj
local notation "pQ" => coefficientShearGluedProjection hπ data Q rQ j hj
local notation "M" => coefficientShearTangentSpecialization hπ data j hj
local notation "σA" => coefficientShearTangentConjugation hπ data j hj

/-- The actual residue-root involution, retaining the original integral coefficient algebra. -/
def tangentResidueConjugationAlgHom : Q →ₐ[R] Q :=
  (nodeTangentConjugation V).toAlgHom.restrictScalars R

/-- Conjugate the entire residue-root equation gluing through its actual coefficient map. -/
def coefficientShearResidueTangentConjugation :=
  coefficientShearSpecialization hπ data Q Q rQ rQ j hj
    (tangentResidueConjugationAlgHom (W := W))
local notation "σQ" => coefficientShearResidueTangentConjugation hπ data j hj

/-- The full residue model conjugation keeps every original integral-model function. -/
@[reassoc] theorem coefficientShearResidueTangentConjugation_projection : σQ ≫ pQ = pQ :=
  coefficientShearSpecialization_projection ..

/-- Its coefficient operation is precisely the original residue tangent conjugation. -/
@[reassoc] theorem coefficientShearResidueTangentConjugation_structure :
    σQ ≫ sQ = sQ ≫ nodeTangentCoverConjugation V :=
  coefficientShearSpecialization_structure ..

/-- The complete residue model operation is an involution, not only on chosen components. -/
@[reassoc] theorem coefficientShearResidueTangentConjugation_involutive :
    σQ ≫ σQ = 𝟙 _ := by
  apply (coefficientShearGlued_isPullback hπ data Q rQ j hj).hom_ext
  · rw [Category.assoc, coefficientShearResidueTangentConjugation_structure,
      coefficientShearResidueTangentConjugation_structure_assoc,
      nodeTangentCoverConjugation_involutive, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, coefficientShearResidueTangentConjugation_projection,
      coefficientShearResidueTangentConjugation_projection, Category.id_comp]

/-- The entire actual tangent residue specialization intertwines the two model involutions. -/
@[reassoc] theorem coefficientShearTangentSpecialization_conjugation :
    σQ ≫ M = M ≫ σA := by
  apply (coefficientShearGlued_isPullback hπ data A rA j hj).hom_ext
  · simp only [Category.assoc, coefficientShearTangentConjugation_structure,
      coefficientShearTangentSpecialization, coefficientShearSpecialization_structure,
      coefficientShearResidueTangentConjugation_structure_assoc,
      coefficientShearSpecialization_structure_assoc]
    apply congrArg (sQ ≫ ·)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (nodeTangentCoefficientMap_conjugation W (residue R)).symm
  · simp only [Category.assoc, coefficientShearTangentConjugation_projection,
      coefficientShearTangentSpecialization, coefficientShearSpecialization_projection,
      coefficientShearResidueTangentConjugation_projection]

end FLT.Mazur.WeierstrassDividedDepth
