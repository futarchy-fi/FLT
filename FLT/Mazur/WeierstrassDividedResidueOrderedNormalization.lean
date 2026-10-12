/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidueTangentNormalization

/-!
# Ordered exterior normalization in the original tangent model

The complete constructed component uses the existing slope normalization.
The actual finite-model conjugation is coefficient conjugation followed by
endpoint reversal, with both original endpoint maps retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [hirr : Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "f" => originalResidueTangentNormalization hπ data j hj d hk hres
local notation "σ" => finiteGlobalTangentConjugation hπ data j hj
variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)

/-- The complete exterior map with the original ordered polygon coordinates. -/
def originalResidueOrderedNormalization :
    scheme Q ⟶ finiteGlobalTensorModel hπ data S j hj :=
  (slopeNormalizationIso a).inv ≫ f

/-- Zero maps to the original first slope marking in the actual finite model. -/
@[reassoc] theorem originalResidueOrderedNormalization_zero :
    zero Q ≫ originalResidueOrderedNormalization hπ data j hj d hk hres a =
      infinitySlopeMark (0 : Q) ≫ f := by
  rw [originalResidueOrderedNormalization, slopeNormalization_inv_zero_assoc]

include ha in
/-- Infinity maps to the original companion slope marking of the same component. -/
@[reassoc] theorem originalResidueOrderedNormalization_infinity :
    infinity Q ≫ originalResidueOrderedNormalization hπ data j hj d hk hres a =
      infinitySlopeMark (-(nodeTangentShear V).a₁) ≫ f := by
  rw [originalResidueOrderedNormalization, slopeNormalization_inv_infinity_assoc, ha]

include ha in
/-- The original finite-model conjugation has the complete ordered exterior reflection formula. -/
@[reassoc] theorem originalResidueOrderedNormalization_reflection :
    nodeTangentLineCoefficients V ≫ endpointReversal Q ≫
        originalResidueOrderedNormalization hπ data j hj d hk hres a =
      originalResidueOrderedNormalization hπ data j hj d hk hres a ≫ σ := by
  apply (cancel_epi (slopeNormalizationIso a).hom).mp
  simp only [originalResidueOrderedNormalization, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← nodeTangentLineConjugation_normalization_assoc V a ha]
  simp only [Iso.hom_inv_id_assoc]
  exact originalResidueTangentNormalization_conjugation hπ data j hj d hk hres

end FLT.Mazur.WeierstrassDividedDepth
