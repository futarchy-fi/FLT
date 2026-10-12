/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueExterior

/-!
# Actual tangent conjugation on the complete glued equations

Transport the original root involution through the full reconstruction.
The complete residue exterior intertwines this involution, including both slope markings.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "root" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "E" => coefficientShearGluedIso hπ data S root j hj
local notation "s" => coefficientShearGluedStructure hπ data S root j hj
local notation "p" => coefficientShearGluedProjection hπ data S root j hj
local notation "σ₀" => finiteGlobalTangentConjugation hπ data j hj

/-- Root exchange on the entire actual tangent-equation gluing. -/
def coefficientShearTangentConjugation := (E).hom ≫ σ₀ ≫ (E).inv
local notation "σ" => coefficientShearTangentConjugation hπ data j hj

/-- The full reconstruction intertwines the original tangent root exchange. -/
@[reassoc] theorem coefficientShearTangentConjugation_reconstruction :
    σ ≫ (E).hom = (E).hom ≫ σ₀ := by
  rw [coefficientShearTangentConjugation, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Root exchange fixes the complete integral-model projection. -/
@[reassoc] theorem coefficientShearTangentConjugation_projection : σ ≫ p = p := by
  rw [coefficientShearGluedProjection, coefficientShearTangentConjugation_reconstruction_assoc]
  exact congrArg (fun f => (E).hom ≫ f)
    (finiteGlobalTangentConjugation_projection hπ data j hj)

/-- Its coefficient operation is the actual conjugation of the integral tangent algebra. -/
@[reassoc] theorem coefficientShearTangentConjugation_structure :
    σ ≫ s = s ≫ nodeTangentCoverConjugation W := by
  rw [coefficientShearGluedStructure, coefficientShearTangentConjugation_reconstruction_assoc,
    Category.assoc]
  exact congrArg (fun f => (E).hom ≫ f)
    (finiteGlobalTangentConjugation_structure hπ data j hj)

/-- The complete model operation is an involution. -/
@[reassoc] theorem coefficientShearTangentConjugation_involutive : σ ≫ σ = 𝟙 _ := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, coefficientShearTangentConjugation_reconstruction,
    coefficientShearTangentConjugation_reconstruction_assoc,
    finiteGlobalTangentConjugation_involutive, Category.comp_id, Category.id_comp]

variable [IsLocalRing R] {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "f" => coefficientShearResidueExterior hπ data j hj d hk hres

/-- The whole residue exterior intertwines the actual glued-model root exchange. -/
@[reassoc] theorem coefficientShearResidueExterior_conjugation :
    nodeTangentLineConjugation V ≫ f = f ≫ σ := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, coefficientShearResidueExterior_reconstruction,
    coefficientShearTangentConjugation_reconstruction,
    coefficientShearResidueExterior_reconstruction_assoc,
    originalResidueTangentNormalization_conjugation]

/-- The first slope marking moves to its companion over the original coefficient exchange. -/
@[reassoc] theorem coefficientShearResidueExterior_first :
    infinitySlopeMark (0 : Q) ≫ f ≫ σ =
      nodeTangentCoverConjugation V ≫ infinitySlopeMark (-(nodeTangentShear V).a₁) ≫ f := by
  rw [← coefficientShearResidueExterior_conjugation, nodeTangentLineConjugation_first_assoc]
  rfl

/-- The companion marking returns to the first, retaining the complete exterior map. -/
@[reassoc] theorem coefficientShearResidueExterior_second :
    infinitySlopeMark (-(nodeTangentShear V).a₁) ≫ f ≫ σ =
      nodeTangentCoverConjugation V ≫ infinitySlopeMark (0 : Q) ≫ f := by
  rw [← coefficientShearResidueExterior_conjugation, nodeTangentLineConjugation_second_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
