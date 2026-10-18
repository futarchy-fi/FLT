/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeSingleExchange

/-!
# The actual exchange operator on target invariant coordinates

The difference of two selected pullbacks is additive. Subtracting a target
correction kills the exchange precisely when its image is the original error.
The zero test uses one omitted label and retains the original chart morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] (o : I) (o' : J)
  (U : (source p q I o).Opens)
  (V : (source p q J o').Opens)
  (hV : ∀ σ, (action e J o' σ).hom ⁻¹ᵁ V = V)
  (h : ∀ ι : J ↪ I, U ≤ subframeMap e o o' ι ⁻¹ᵁ V)

/-- Difference of actual selected pullbacks, on the target invariant ring. -/
def subframeSelectionDifference (ι κ : J ↪ I) :
    invariantCoordinates (restrictedAction (action e J o') V hV) →+ Γ(U.toScheme, ⊤) where
  toFun v := (subframeRefinementMap e o o' κ U V (h κ)).appTop v.val -
    (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val
  map_zero' := by simp only [ZeroMemClass.coe_zero, map_zero, sub_zero]
  map_add' v w := by
    simp only [Subring.coe_add, map_add]
    abel

omit [DecidableEq I] in
/-- Changing the reference selection adds the two successive errors. -/
theorem subframeSelectionDifference_cocycle (ι κ μ : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeSelectionDifference e o o' U V hV h ι μ v =
      subframeSelectionDifference e o o' U V hV h ι κ v +
        subframeSelectionDifference e o o' U V hV h κ μ v := by
  dsimp only [subframeSelectionDifference, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  abel

/-- The one selected-to-omitted exchange operator. -/
def subframeExchangeMap (ι : J ↪ I) (b₀ : I) :
    invariantCoordinates (restrictedAction (action e J o') V hV) →+ Γ(U.toScheme, ⊤) :=
  subframeSelectionDifference e o o' U V hV h ι
    (ι.trans (Equiv.swap (ι o') b₀).toEmbedding)

/-- Target corrections solve the exchange by matching its actual error. -/
theorem subframeExchangeMap_sub_eq_zero_iff (ι : J ↪ I) (b₀ : I)
    (v z : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeExchangeMap e o o' U V hV h ι b₀ (v - z) = 0 ↔
      subframeExchangeMap e o o' U V hV h ι b₀ z =
        subframeExchangeMap e o o' U V hV h ι b₀ v := by
  rw [map_sub, sub_eq_zero, eq_comm]

/-- No degree hypothesis is needed to detect invariance with the exchange operator. -/
theorem subframeExchangeMap_zero_iff_invariant
    (hU : ∀ σ, (action e I o σ).hom ⁻¹ᵁ U = U)
    (ι : J ↪ I) (b₀ : I) (hb₀ : b₀ ∉ Set.range ι)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    subframeExchangeMap e o o' U V hV h ι b₀ v = 0 ↔
      ∃ w : invariantCoordinates (restrictedAction (action e I o) U hU),
        w.val = (subframeRefinementMap e o o' ι U V (h ι)).appTop v.val := by
  rw [subframePullback_invariant_iff_one_exchange e o o' U hU V hV h ι b₀ hb₀]
  exact sub_eq_zero

end FLT.Mazur.EquivalenceRelationNormalizedFrames
