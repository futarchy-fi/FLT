/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationOpenChartScalars
public import FLT.Mazur.EquivalenceRelationSubframeExchangeMap

/-!
# Original scalar compatibility along every selected subframe

The actual coordinate arrow compares the two distinguished endpoints. Original
invariance therefore makes scalar pullbacks independent of the selection, even
for strict subframes. Multiplying a target section scales its exchange error.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (W : A.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)
  (s : Γ(W.toScheme, ⊤)) (hs : (p ∣_ W).appTop s = (q.resLE W _ hW.le).appTop s)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (hUW : U ≤ first p q I o ⁻¹ᵁ W)
  (V : (source p q J o').Opens) (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (hVW : V ≤ first p q J o' ⁻¹ᵁ W)

/-- Every selected pullback preserves the actual original scalar coefficient. -/
theorem openChartScalar_subframe (ι : J ↪ I) (h : U ≤ subframeMap e o o' ι ⁻¹ᵁ V) :
    (subframeRefinementMap e o o' ι U V h).appTop
      (openChartScalar e W hW s hs o' V hV hVW).val =
        (openChartScalar e W hW s hs o U hU hUW).val := by
  symm
  apply open_scalar_test W hW s hs
    ((first p q I o).resLE W U hUW)
    (subframeRefinementMap e o o' ι U V h ≫ (first p q J o').resLE W V hVW)
    (U.ι ≫ coordinate p q I o (ι o'))
  · simp only [Category.assoc, coordinate_first, Scheme.Hom.resLE_comp_ι]
  · simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
      subframeRefinementMap_inclusion_assoc, subframeMap_first]

variable [DecidableEq I] (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
  (ι : J ↪ I) (b₀ : I)

/-- Exchange is linear under multiplication by any original invariant scalar. -/
theorem subframeExchangeMap_scalar_mul
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeExchangeMap e o o' U V hV h ι b₀
      (openChartScalar e W hW s hs o' V hV hVW * v) =
        (openChartScalar e W hW s hs o U hU hUW).val *
          subframeExchangeMap e o o' U V hV h ι b₀ v := by
  dsimp only [subframeExchangeMap, subframeSelectionDifference,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  simp only [Subring.coe_mul, map_mul,
    openChartScalar_subframe e W hW s hs o o' U hU hUW V hV hVW, mul_sub]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
