/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentSplitNormalizationComparison
public import FLT.Mazur.WeierstrassDividedResidueFiniteNormalization

/-!
# The original nonsplit residue component has the actual split cubic projection

Specialize the complete root-shear comparison to the original divided model.
The result is a concrete complete cubic map that determines its finite lift.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  {k : ℕ} (d : Data W π k) (hk : 0 < k) (hres : residue R π = 0)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
variable [hirr : Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "h" => originalResidue_normalization_coefficients d hk hres
local notation "b" => nodeTangentShear_normalization_coefficients V (h).1 (h).2.1 (h).2.2
local notation "U" => nodeTangentShear V
local notation "C₀" => WeierstrassCurve.VariableChange.mk (1 : Qˣ) 0
  (AdjoinRoot.root (nodeTangentPolynomial V)) 0

/-- The complete split normalization with the actual shear and original coefficient projections. -/
def originalResidueSplitCubic : scheme Q ⟶ integralCurve W :=
  splitCompleteNormalization U (b).1 (b).2.1 (b).2.2.1 (b).2.2.2 ≫
    (integralVariableChangeIso ((V).map (algebraMap (ResidueField R) Q)) U C₀ rfl).hom ≫
      integralCoefficientMorphism V ≫ integralCoefficientMorphism W

omit [IsDomain R] [IsBezout R] in
/-- The constructed original root normalization is this complete split cubic map. -/
theorem originalResidueCompleteNormalization_eq_splitCubic :
    originalResidueCompleteNormalization d hk hres = originalResidueSplitCubic d hk hres := by
  rw [originalResidueCompleteNormalization, nodeTangentCompleteNormalization_eq_split]
  simp only [originalResidueSplitCubic, Category.assoc]

omit [IsDomain R] [IsBezout R] in
/-- Its entire affine restriction is the original unsheared normalization algebra map. -/
@[reassoc] theorem originalResidueSplitCubic_left :
    left Q ≫ originalResidueSplitCubic d hk hres =
      originalResidueNormalizationMap d hk hres ≫ integralCurveChart W 2 := by
  rw [← originalResidueCompleteNormalization_eq_splitCubic,
    originalResidueCompleteNormalization_left]

/-- Every finite stage retains this complete split-shear cubic projection. -/
@[reassoc] theorem originalResidueFiniteNormalization_splitCubic :
    originalResidueFiniteNormalization hπ data j hj d hk hres ≫
        finiteGlobalContraction hπ data j hj = originalResidueSplitCubic d hk hres := by
  rw [originalResidueFiniteNormalization_contraction,
    originalResidueCompleteNormalization_eq_splitCubic]

/-- A candidate complete split component is the original one once its cubic map is checked. -/
theorem originalResidueSplitCubic_finite_unique
    (f : scheme Q ⟶ finiteGlobalModel hπ data j hj)
    (hf : f ≫ finiteGlobalContraction hπ data j hj = originalResidueSplitCubic d hk hres) :
    f = originalResidueFiniteNormalization hπ data j hj d hk hres := by
  apply originalResidueFiniteNormalization_unique
  rw [originalResidueCompleteNormalization_eq_splitCubic]
  exact hf

/-- The actual finite exterior is the proper lift of the explicit split-shear cubic map. -/
theorem originalResidueFiniteNormalization_eq_splitLift :
    originalResidueFiniteNormalization hπ data j hj d hk hres =
      projectiveFiniteLift hπ data j hj (originalResidueNormalization d hk hres)
        (originalResidueNormalization_x_regular d hk hres)
        (originalResidueSplitCubic d hk hres) (originalResidueSplitCubic_left d hk hres) := by
  symm
  apply originalResidueSplitCubic_finite_unique
  exact projectiveFiniteLift_contraction _ _ _ _ _ _ _ _

end FLT.Mazur.WeierstrassDividedDepth
