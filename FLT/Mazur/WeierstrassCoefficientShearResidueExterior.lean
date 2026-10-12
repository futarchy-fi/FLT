/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearGluing
public import FLT.Mazur.WeierstrassDividedResidueTangentNormalization
public import FLT.Mazur.WeierstrassDividedResidueSplitCubic

/-!
# The complete residue exterior in the glued tangent equations

The original residue normalization gives a complete component of the sheared
equation gluing. Its actual coefficient specialization and split cubic projection
determine the complete map uniquely.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "root" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "E" => coefficientShearGluedIso hπ data S root j hj
local notation "s" => coefficientShearGluedStructure hπ data S root j hj
local notation "p" => coefficientShearGluedProjection hπ data S root j hj
local notation "c" => Spec.map (CommRingCat.ofHom (nodeTangentCoefficientMap W (residue R)))

/-- The whole original residue exterior in the complete sheared tangent-equation gluing. -/
def coefficientShearResidueExterior :
    scheme Q ⟶ coefficientShearGlued hπ data S root j hj :=
  originalResidueTangentNormalization hπ data j hj d hk hres ≫ (E).inv

/-- Reconstruction gives the original complete tangent normalization, with no chart restriction. -/
@[reassoc] theorem coefficientShearResidueExterior_reconstruction :
    coefficientShearResidueExterior hπ data j hj d hk hres ≫ (E).hom =
      originalResidueTangentNormalization hπ data j hj d hk hres := by
  rw [coefficientShearResidueExterior, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The coefficient leg is the actual specialization of the original integral root algebra. -/
@[reassoc] theorem coefficientShearResidueExterior_structure :
    coefficientShearResidueExterior hπ data j hj d hk hres ≫ s = toBase Q ≫ c := by
  rw [coefficientShearGluedStructure, coefficientShearResidueExterior_reconstruction_assoc]
  exact originalResidueTangentNormalization_structure hπ data j hj d hk hres

/-- The complete exterior retains the original finite normalization morphism. -/
@[reassoc] theorem coefficientShearResidueExterior_projection :
    coefficientShearResidueExterior hπ data j hj d hk hres ≫ p =
      originalResidueFiniteNormalization hπ data j hj d hk hres := by
  rw [coefficientShearGluedProjection, coefficientShearResidueExterior_reconstruction_assoc]
  exact originalResidueTangentNormalization_projection hπ data j hj d hk hres

/-- The entire exterior contracts by the actual split cubic, shear, and coefficient morphisms. -/
@[reassoc] theorem coefficientShearResidueExterior_toCurve :
    coefficientShearResidueExterior hπ data j hj d hk hres ≫ p ≫
        finiteGlobalContraction hπ data j hj = originalResidueSplitCubic d hk hres := by
  rw [coefficientShearResidueExterior_projection_assoc,
    originalResidueFiniteNormalization_splitCubic]

/-- The actual coefficient leg and complete split cubic determine this whole exterior uniquely. -/
theorem coefficientShearResidueExterior_unique
    (f : scheme Q ⟶ coefficientShearGlued hπ data S root j hj)
    (hs : f ≫ s = toBase Q ≫ c)
    (hc : f ≫ p ≫ finiteGlobalContraction hπ data j hj =
      originalResidueSplitCubic d hk hres) :
    f = coefficientShearResidueExterior hπ data j hj d hk hres := by
  apply (coefficientShearGlued_isPullback hπ data S root j hj).hom_ext
  · rw [hs, coefficientShearResidueExterior_structure]
  · rw [coefficientShearResidueExterior_projection]
    apply originalResidueSplitCubic_finite_unique
    simpa only [Category.assoc] using hc

end FLT.Mazur.WeierstrassDividedDepth
