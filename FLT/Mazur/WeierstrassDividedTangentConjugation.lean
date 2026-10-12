/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentCoefficientCover
public import FLT.Mazur.WeierstrassDividedCoefficientInputs
public import FLT.Mazur.WeierstrassDividedFaithfulActionDescent

/-!
# The actual finite model over the quadratic tangent cover

The canonical root exchange gives an involution of the original whole
coefficient model and its smooth action domain. The integral action is
equivariant, and the same concrete coefficient cover detects equality of
whole-model actions by faithful flatness.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j ≤ n)
local notation "S" => AdjoinRoot (nodeTangentPolynomial W)
local notation "q" => nodeTangentCover W
local notation "σ" => nodeTangentCoverConjugation W
local notation "hσ" => nodeTangentCoverConjugation_structure W
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "fst" => pullback.fst q base
local notation "snd" => pullback.snd q base
local notation "a" => finiteGlobalCoefficientAction hπ data j hj S
local notation "d" => finiteGlobalCoefficientDomainSymmetry hπ data j hj S σ hσ

/-- The canonical root exchange on the whole actual tangent-coefficient model. -/
def finiteGlobalTangentConjugation :
    finiteGlobalTensorModel hπ data S j hj ⟶ finiteGlobalTensorModel hπ data S j hj :=
  finiteGlobalCoefficientSymmetry hπ data j hj S σ hσ

/-- Its base operation is the actual conjugation of the splitting algebra. -/
@[reassoc] theorem finiteGlobalTangentConjugation_structure :
    finiteGlobalTangentConjugation hπ data j hj ≫ fst = fst ≫ σ :=
  finiteGlobalCoefficientSymmetry_structure hπ data j hj S σ hσ

/-- Its projection is the original integral finite model, with every marking retained. -/
@[reassoc] theorem finiteGlobalTangentConjugation_projection :
    finiteGlobalTangentConjugation hπ data j hj ≫ snd = snd :=
  finiteGlobalCoefficientSymmetry_projection hπ data j hj S σ hσ

/-- The concrete root exchange squares to the identity on the whole finite model. -/
@[reassoc] theorem finiteGlobalTangentConjugation_involutive :
    finiteGlobalTangentConjugation hπ data j hj ≫
      finiteGlobalTangentConjugation hπ data j hj = 𝟙 _ :=
  finiteGlobalCoefficientSymmetry_involutive hπ data j hj S σ hσ
    (nodeTangentCoverConjugation_involutive W)

/-- Root exchange is an involution over the original finite model itself. -/
def finiteGlobalTangentConjugationIso : Over.mk snd ≅ Over.mk snd :=
  Over.isoMk
    { hom := finiteGlobalTangentConjugation hπ data j hj
      inv := finiteGlobalTangentConjugation hπ data j hj
      hom_inv_id := finiteGlobalTangentConjugation_involutive hπ data j hj
      inv_hom_id := finiteGlobalTangentConjugation_involutive hπ data j hj }
    (finiteGlobalTangentConjugation_projection hπ data j hj)

/-- The actual finite-model action is equivariant for the canonical tangent root exchange. -/
theorem finiteGlobalTangentConjugation_action :
    d ≫ a = a ≫ finiteGlobalTangentConjugation hπ data j hj :=
  finiteGlobalCoefficientAction_symmetry hπ data j hj S σ hσ

/-- The actual tangent-coefficient action domain also has an involutive root exchange. -/
@[reassoc] theorem finiteGlobalTangentDomainConjugation_involutive : d ≫ d = 𝟙 _ :=
  finiteGlobalCoefficientDomainSymmetry_involutive hπ data j hj S σ hσ
    (nodeTangentCoverConjugation_involutive W)

/-- Equality with the integral action is detected on this concrete quadratic tangent cover. -/
theorem finiteGlobalAction_eq_of_tangentCover
    (b : finiteGlobalActionProduct hπ data j hj ⟶ finiteGlobalModel hπ data j hj)
    (hb : finiteGlobalCoefficientActionProduct hπ data j hj S ≫ b = a ≫ snd) :
    b = finiteGlobalAction hπ data j hj :=
  finiteGlobalAction_eq_of_coefficient hπ data j hj S (nodeTangentAlgebra_faithfullyFlat W) b hb

end FLT.Mazur.WeierstrassDividedDepth
