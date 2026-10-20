/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResolvedNegation
public import FLT.Mazur.WeierstrassDividedGlobalOriginalSmoothPoints
public import FLT.Mazur.WeierstrassDividedResolvedSmoothAction

/-!
# Insert the original group in the entire resolved smooth locus

The actual original smooth embedding lands in the full resolved smooth open.
It keeps its inclusion, coefficients, inverse and original addition. This is
the open chart needed on each factor of the resolved multiplication domain.
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

/-- The original smooth group embeds in the full resolved smooth locus. -/
def finiteOriginalToResolved : (integralSmoothOpen W).toScheme ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (finiteGlobalSmoothEmbedding hπ data j hj) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have he : finiteGlobalSmoothEmbedding hπ data j hj ⁻¹ᵁ U = ⊤ := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    exact he.ge (Set.mem_univ x))

instance finiteOriginalToResolved_isOpenImmersion :
    IsOpenImmersion (finiteOriginalToResolved hπ data j hj) := by
  unfold finiteOriginalToResolved
  infer_instance

/-- The open embedding retains the exact original finite-model inclusion. -/
@[reassoc] theorem finiteOriginalToResolved_inclusion :
    finiteOriginalToResolved hπ data j hj ≫ (U).ι =
      finiteGlobalSmoothEmbedding hπ data j hj := IsOpenImmersion.lift_fac _ _ _

/-- The original coefficient morphism is retained inside the full resolved smooth locus. -/
@[reassoc] theorem finiteOriginalToResolved_structure :
    finiteOriginalToResolved hπ data j hj ≫ (U).ι ≫ base = integralSmoothStructure W := by
  rw [finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_structure]

/-- Both original and resolved inverse maps agree on this actual open subgroup chart. -/
@[reassoc] theorem finiteOriginalToResolved_negation :
    finiteOriginalToResolved hπ data j hj ≫ finiteResolvedNegation hπ data j hj =
      integralSmoothNegation W ≫ finiteOriginalToResolved hπ data j hj := by
  apply (cancel_mono (U).ι).mp
  rw [Category.assoc, finiteResolvedNegation_inclusion,
    finiteOriginalToResolved_inclusion_assoc, finiteGlobalSmoothEmbedding_negation,
    Category.assoc, finiteOriginalToResolved_inclusion]

/-- The action on the original open chart is the same original addition. -/
theorem finiteGlobalSmoothPointAction_original {T : Scheme}
    (a b : T ⟶ (integralSmoothOpen W).toScheme)
    (h : a ≫ integralSmoothStructure W = b ≫ integralSmoothStructure W) :
    finiteGlobalSmoothPointAction hπ data j hj a (b ≫ finiteOriginalToResolved hπ data j hj)
        (by rw [Category.assoc, finiteOriginalToResolved_structure]; exact h) =
      smoothPairPointAddition W a b h ≫ finiteOriginalToResolved hπ data j hj := by
  apply (cancel_mono (U).ι).mp
  simp only [finiteGlobalSmoothPointAction_inclusion, Category.assoc,
    finiteOriginalToResolved_inclusion]
  exact finiteGlobalPointAction_smoothEmbedding hπ data j hj a b h

end FLT.Mazur.WeierstrassDividedDepth
