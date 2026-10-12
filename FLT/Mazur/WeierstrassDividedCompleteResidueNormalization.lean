/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentCompleteNormalization
public import FLT.Mazur.WeierstrassDividedResidueNormalization
public import FLT.Mazur.WeierstrassIntegralCoefficientMap

/-!
# Complete normalization of the original divided residue cubic

Extend the actual residue normalization across infinity and retain the original
integral cubic via its coefficient morphism. Its x coordinate is regular, as
needed to lift this complete map through every actual finite modification.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : Data W π k) (hk : 0 < k) (hπ : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [hirr : Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "h" => originalResidue_normalization_coefficients d hk hπ

/-- The complete actual residue normalization, with the original integral target. -/
def originalResidueCompleteNormalization : scheme Q ⟶ integralCurve W :=
  nodeTangentCompleteNormalization V (h).1 (h).2.1 (h).2.2 ≫
    integralCoefficientMorphism (S := ResidueField R) W

/-- The extension retains every original function on the whole affine normalization chart. -/
@[reassoc] theorem originalResidueCompleteNormalization_left :
    left Q ≫ originalResidueCompleteNormalization d hk hπ =
      originalResidueNormalizationMap d hk hπ ≫ integralCurveChart W 2 := by
  rw [originalResidueCompleteNormalization, nodeTangentCompleteNormalization_left_assoc,
    nodeTangentAffineToCubic, Category.assoc]
  erw [integralCurveChart_coefficientMorphism]
  change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ _
  rw [← Spec.map_comp_assoc]
  rfl

/-- The complete morphism preserves the actual integral-to-residue coefficient projection. -/
@[reassoc] theorem originalResidueCompleteNormalization_base :
    originalResidueCompleteNormalization d hk hπ ≫ integralCurveStructure W =
      toBase Q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (ResidueField R) Q).comp (residue R))) := by
  rw [originalResidueCompleteNormalization, Category.assoc,
    integralCoefficientMorphism_structure]
  erw [nodeTangentCompleteNormalization_base_assoc]
  rw [← Spec.map_comp]
  rfl

/-- Actual root exchange fixes the entire original projective cubic projection. -/
@[reassoc] theorem originalResidueCompleteNormalization_conjugation :
    nodeTangentLineConjugation V ≫ originalResidueCompleteNormalization d hk hπ =
      originalResidueCompleteNormalization d hk hπ := by
  rw [originalResidueCompleteNormalization, nodeTangentCompleteNormalization_conjugation_assoc]

/-- The original x coordinate pulls back to a monic polynomial of degree two. -/
theorem originalResidueNormalization_x_monic :
    (originalResidueNormalization d hk hπ (coord W 2 0)).Monic := by
  rw [originalResidueNormalization_coord]
  change (X * (X + C (nodeTangentShear V).a₁) : Polynomial Q).Monic
  exact monic_X.mul (monic_X_add_C _)

/-- The unchanged original D(x) pulls back to a schematically dense normalization open. -/
theorem originalResidueNormalization_x_regular :
    IsRegular (originalResidueNormalization d hk hπ (coord W 2 0)) :=
  (originalResidueNormalization_x_monic d hk hπ).isRegular

end FLT.Mazur.WeierstrassDividedDepth
