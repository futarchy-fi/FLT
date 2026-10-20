/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegationInitial
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat

/-!
# Negation on every resolved smooth component

The constructed entire-model involution preserves the full relative smooth
locus. Its restriction includes the new resolved components and retains the
original cubic, coefficients and original smooth inverse.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus

/-- The original negation automorphism preserves the relative smooth locus exactly. -/
theorem finiteGlobalNegation_preimage_smooth :
    finiteGlobalNegation hπ data j hj ⁻¹ᵁ U = U := by
  let _ : IsIso (finiteGlobalNegation hπ data j hj) :=
    (finiteGlobalNegationIso hπ data j hj).isIso_hom
  simp only [Scheme.Hom.preimage_smoothLocus_eq,
    finiteGlobalNegation_structure]

/-- Restrict the original global negation to the actual relative smooth open. -/
def finiteResolvedNegation : (U).toScheme ⟶
    (U).toScheme :=
  IsOpenImmersion.lift (U).ι
    ((U).ι ≫ finiteGlobalNegation hπ data j hj) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      have h : x.val ∈
          finiteGlobalNegation hπ data j hj ⁻¹ᵁ U := by
        rw [finiteGlobalNegation_preimage_smooth]
        exact x.property
      exact h)

/-- The restricted operation retains the actual cubic negation. -/
@[reassoc (attr := simp)] theorem finiteResolvedNegation_inclusion :
    finiteResolvedNegation hπ data j hj ≫ (U).ι =
      (U).ι ≫ finiteGlobalNegation hπ data j hj :=
  IsOpenImmersion.lift_fac _ _ _

/-- Restricted negation is still defined over the original coefficient ring. -/
@[reassoc] theorem finiteResolvedNegation_structure :
    finiteResolvedNegation hπ data j hj ≫ (U).ι ≫ base = (U).ι ≫ base := by
  rw [← Category.assoc, finiteResolvedNegation_inclusion,
    Category.assoc, finiteGlobalNegation_structure]

/-- Negation is an involution on the actual smooth locus. -/
@[reassoc (attr := simp)] theorem finiteResolvedNegation_comp :
    finiteResolvedNegation hπ data j hj ≫ finiteResolvedNegation hπ data j hj = 𝟙 _ := by
  apply (cancel_mono (U).ι).mp
  simp only [Category.assoc, finiteResolvedNegation_inclusion, Category.id_comp,
    finiteResolvedNegation_inclusion_assoc, finiteGlobalNegation_comp, Category.comp_id]

/-- The restricted involution is an actual scheme automorphism. -/
def finiteResolvedNegationIso : (U).toScheme ≅
    (U).toScheme where
  hom := finiteResolvedNegation hπ data j hj
  inv := finiteResolvedNegation hπ data j hj
  hom_inv_id := finiteResolvedNegation_comp hπ data j hj
  inv_hom_id := finiteResolvedNegation_comp hπ data j hj

/-- The resolved inverse retains the exact original projective cubic inverse. -/
@[reassoc] theorem finiteResolvedNegation_contraction :
    finiteResolvedNegation hπ data j hj ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (U).ι ≫ finiteGlobalContraction hπ data j hj ≫ integralCurveNegation W := by
  rw [finiteResolvedNegation_inclusion_assoc, finiteGlobalNegation_contraction]

omit [IsNoetherianRing R] in
/-- Original smooth inputs retain precisely their original negative in every entire model. -/
@[reassoc] theorem finiteGlobalSmoothEmbedding_negation :
    finiteGlobalSmoothEmbedding hπ data j hj ≫ finiteGlobalNegation hπ data j hj =
      integralSmoothNegation W ≫ finiteGlobalSmoothEmbedding hπ data j hj := by
  apply finiteGlobal_eq_smoothEmbedding hπ data j hj (integralSmoothNegation W)
  rw [Category.assoc, finiteGlobalNegation_contraction,
    finiteGlobalSmoothEmbedding_contraction_assoc, integralSmoothNegation_inclusion]

end FLT.Mazur.WeierstrassDividedDepth
