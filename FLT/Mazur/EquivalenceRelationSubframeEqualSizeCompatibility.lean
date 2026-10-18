/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeEqualSize

/-!
# Compatible equal-size transfers from one independent target

Transfers of one invariant target section to independent source charts agree
along every actual equal-size subframe refinement. The intermediate source
charts need not be restrictions of one another. This supplies compatible
same-size families; strict-size changes are outside this result.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
  (o : I) (o' : J) (o'' : H)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (T : (source p q H o'').Opens)
  (hT : ∀ σ, (action e H o'' σ).hom ⁻¹ᵁ T = T)
  (hUT : ∀ ι : H ↪ I, U ≤ subframeMap e o o'' ι ⁻¹ᵁ T)
  (hVT : ∀ ι : H ↪ J, V ≤ subframeMap e o' o'' ι ⁻¹ᵁ T)
  (hcI : Fintype.card I = Fintype.card H) (hcJ : Fintype.card J = Fintype.card H)
  (hNU : IsUnit ((Fintype.card I).choose (Fintype.card H) : Γ(U.toScheme, ⊤)))
  (hNV : IsUnit ((Fintype.card J).choose (Fintype.card H) : Γ(V.toScheme, ⊤)))

include hcI hcJ in
/-- Independent source transfers from a common equal-size target respect every refinement. -/
theorem subframeNormalizedTransfer_equal_size_refinement
    (κ : J ↪ I) (hUV : U ≤ subframeMap e o o' κ ⁻¹ᵁ V)
    (w : invariantCoordinates (restrictedAction (action e H o'') T hT)) :
    (subframeNormalizedTransfer e o o'' U hU T hT hUT hNU w).val =
      (subframeRefinementMap e o o' κ U V hUV).appTop
        (subframeNormalizedTransfer e o' o'' V hV T hT hVT hNV w).val := by
  let θ : H ↪ J := (Fintype.equivOfCardEq hcJ.symm).toEmbedding
  rw [subframeNormalizedTransfer_eq_of_card_eq e o o'' U hU T hT hUT hcI hNU
      (θ.trans κ) w,
    subframeNormalizedTransfer_eq_of_card_eq e o' o'' V hV T hT hVT hcJ hNV θ w,
    subframeRefinement_appTop_comp e o o' κ U V hUV o'' θ T (hVT θ) (hUT (θ.trans κ))]

variable [Etale p]
open MixedFrames

include hcI hcJ in
/-- Common-target equal-size lifts agree on each actual original embedding branch. -/
theorem subframeNormalizedTransfer_equal_size_branch
    (κ : J ↪ I) (hUV : U ≤ subframeMap e o o' κ ⁻¹ᵁ V)
    (w : invariantCoordinates (restrictedAction (action e H o'') T hT)) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
      mixedChartFirst o o' U V).appTop
        (subframeNormalizedTransfer e o o'' U hU T hT hUT hNU w).val =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
      mixedChartSecond o o' U V).appTop
        (subframeNormalizedTransfer e o' o'' V hV T hT hVT hNV w).val := by
  apply (mixedSubframeBranch_equation_iff e o o' U V κ hUV _ _).mpr
  exact subframeNormalizedTransfer_equal_size_refinement
    e o o' o'' U hU V hV T hT hUT hVT hcI hcJ hNU hNV κ hUV w

end FLT.Mazur.EquivalenceRelationNormalizedFrames
