/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTangentConjugation
public import FLT.Mazur.WeierstrassDividedResidueOrderedNormalization

/-!
# Ordered exterior reflection in the actual coefficient gluing

The full exterior retains the original ordered polygon coordinates. Actual
integral tangent conjugation acts by coefficient conjugation and endpoint reversal.
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

variable [IsLocalRing R] {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "σ" => coefficientShearTangentConjugation hπ data j hj
variable (a : (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) =
    (nodeTangentShear (W.map (residue R))).a₁)

/-- The complete coefficient exterior with the original ordered polygon parameter. -/
def coefficientShearResidueOrderedExterior :
    scheme Q ⟶ coefficientShearGlued hπ data S root j hj :=
  (slopeNormalizationIso a).inv ≫ coefficientShearResidueExterior hπ data j hj d hk hres
local notation "f" => coefficientShearResidueOrderedExterior hπ data j hj d hk hres a

/-- Reconstruction retains the complete original ordered exterior morphism. -/
@[reassoc] theorem coefficientShearResidueOrderedExterior_original :
    f ≫ (E).hom = originalResidueOrderedNormalization hπ data j hj d hk hres a := by
  rw [coefficientShearResidueOrderedExterior, Category.assoc,
    coefficientShearResidueExterior_reconstruction]
  rfl

/-- The zero marking is the original first slope marking of the full exterior. -/
@[reassoc] theorem coefficientShearResidueOrderedExterior_zero :
    zero Q ≫ f = infinitySlopeMark (0 : Q) ≫
      coefficientShearResidueExterior hπ data j hj d hk hres := by
  rw [coefficientShearResidueOrderedExterior, slopeNormalization_inv_zero_assoc]

include ha in
/-- Infinity is the original companion marking, with its signed tangent slope. -/
@[reassoc] theorem coefficientShearResidueOrderedExterior_infinity :
    infinity Q ≫ f = infinitySlopeMark (-(nodeTangentShear V).a₁) ≫
      coefficientShearResidueExterior hπ data j hj d hk hres := by
  rw [coefficientShearResidueOrderedExterior, slopeNormalization_inv_infinity_assoc, ha]

include ha in
/-- Actual tangent conjugation has the full ordered reflection formula in the glued model. -/
@[reassoc] theorem coefficientShearResidueOrderedExterior_reflection :
    nodeTangentLineCoefficients V ≫ endpointReversal Q ≫ f = f ≫ σ := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, coefficientShearResidueOrderedExterior_original,
    coefficientShearTangentConjugation_reconstruction,
    coefficientShearResidueOrderedExterior_original_assoc,
    originalResidueOrderedNormalization_reflection hπ data j hj d hk hres a ha]

/-- The entire ordered exterior contracts to the original split cubic with the same parameter. -/
@[reassoc] theorem coefficientShearResidueOrderedExterior_toCurve :
    f ≫ p ≫ finiteGlobalContraction hπ data j hj =
      (slopeNormalizationIso a).inv ≫ originalResidueSplitCubic d hk hres := by
  rw [coefficientShearResidueOrderedExterior, Category.assoc,
    coefficientShearResidueExterior_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
