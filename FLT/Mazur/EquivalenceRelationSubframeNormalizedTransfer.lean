/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeTransferGraphErrors
public import FLT.Mazur.UnitNaturalDivision

/-!
# Unscaled invariant subframe transfer on the unit-degree locus

Divide the unordered transfer by its binomial degree when that degree is a unit
on the actual source chart. The resulting invariant section solves an original
unscaled embedding equation precisely when the corresponding transfer error
vanishes. Invertibility alone does not assert that vanishing.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
  (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)
local notation "N" => Nat.choose (Fintype.card I) (Fintype.card J)
variable (hN : IsUnit
  (Nat.choose (Fintype.card I) (Fintype.card J) : Γ(U.toScheme, ⊤)))

/-- Divide the transfer on the actual source ring; invariance follows by cancellation. -/
def subframeNormalizedTransfer
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    invariantCoordinates (restrictedAction (action e I o) U hU) :=
  ⟨UnitNaturalDivision.divide N hN (subframeTransferSection e o o' U V hV h v), by
    intro σ
    rw [SchemeCoordinateAction.coordinateAction_smul]
    apply UnitNaturalDivision.nsmul_injective N hN
    dsimp only
    rw [← map_nsmul, UnitNaturalDivision.nsmul_divide]
    exact subframeTransferSection_invariant e o o' U hU V hV h v σ⟩

/-- The new invariant section recovers the original transfer on multiplying by its degree. -/
theorem nsmul_subframeNormalizedTransfer
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    N • subframeNormalizedTransfer e o o' U hU V hV h hN v =
      subframeTransfer e o o' U hU V hV h v := by
  apply Subtype.ext
  exact UnitNaturalDivision.nsmul_divide N hN _

/-- Exact normalization is additive in independently chosen target lifts. -/
theorem subframeNormalizedTransfer_add
    (v w : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeNormalizedTransfer e o o' U hU V hV h hN (v + w) =
      subframeNormalizedTransfer e o o' U hU V hV h hN v +
        subframeNormalizedTransfer e o o' U hU V hV h hN w := by
  apply Subtype.ext
  change UnitNaturalDivision.divide N hN
    (subframeTransferSection e o o' U V hV h (v + w)) = _
  have ht := congrArg Subtype.val ((subframeTransfer e o o' U hU V hV h).map_add v w)
  change subframeTransferSection e o o' U V hV h (v + w) =
    subframeTransferSection e o o' U V hV h v + subframeTransferSection e o o' U V hV h w
      at ht
  rw [ht, map_add]
  rfl

/-- The selection-error criterion now characterizes the unscaled section equation. -/
theorem subframeNormalizedTransfer_selection_iff (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
      (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val ↔
        subframeTransferSelectionError e o o' U V hV h ι v = 0 := by
  change UnitNaturalDivision.divide N hN _ = _ ↔ _
  rw [UnitNaturalDivision.divide_eq_iff]
  exact sub_eq_zero.symm

variable [Etale p]
open MixedFrames

/-- The normalized transfer solves the original unscaled graph iff its error is zero. -/
theorem subframeNormalizedTransfer_branch_iff (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartFirst o o' U V).appTop
        (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
    ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι ι).ι ≫
      mixedChartSecond o o' U V).appTop v.val ↔
        subframeTransferSelectionError e o o' U V hV h ι v = 0 := by
  rw [mixedSubframeBranch_equation_iff e o o' U V ι (h ι)]
  exact subframeNormalizedTransfer_selection_iff e o o' U hU V hV h hN ι v

end FLT.Mazur.EquivalenceRelationNormalizedFrames
