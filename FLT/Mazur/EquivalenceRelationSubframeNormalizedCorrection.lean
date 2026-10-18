/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeNormalizedTransfer

/-!
# Unscaled transfer corrections and their original boundary

The normalized transfer lifts the original boundary coefficient whenever the
unnormalized transfer lifts its degree multiple. The resulting correction is
an actual invariant kernel element. The unscaled graph obstruction remains
exactly one representative selection error on a stable all-selection domain.
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
  (hN : IsUnit (Nat.choose (Fintype.card I) (Fintype.card J) : Γ(U.toScheme, ⊤)))
local notation "N" => Nat.choose (Fintype.card I) (Fintype.card J)

/-- The correction to an independent original, unscaled source lift. -/
def subframeNormalizedCorrection
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    invariantCoordinates (restrictedAction (action e I o) U hU) :=
  u - subframeNormalizedTransfer e o o' U hU V hV h hN v

/-- Multiplying the unscaled correction gives precisely the original transfer correction. -/
theorem nsmul_subframeNormalizedCorrection
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    N • subframeNormalizedCorrection e o o' U hU V hV h hN u v =
      subframeTransferCorrection e o o' U hU V hV h u v := by
  rw [subframeNormalizedCorrection, nsmul_sub, nsmul_subframeNormalizedTransfer]
  rfl

/-- Any exact scaled boundary formula becomes the original unscaled formula. -/
theorem subframeNormalizedTransfer_map {S : Type*} [CommRing S]
    (f : Γ(U.toScheme, ⊤) →+* S) (t : S)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV))
    (hv : f (subframeTransferSection e o o' U V hV h v) = N • t) :
    f (subframeNormalizedTransfer e o o' U hU V hV h hN v).val = t :=
  UnitNaturalDivision.map_divide_eq N hN f _ t hv

/-- The correction vanishes on the entire original boundary, without reducing it. -/
theorem subframeNormalizedCorrection_map_zero {S : Type*} [CommRing S]
    (f : Γ(U.toScheme, ⊤) →+* S) (t : S)
    (u : invariantCoordinates (restrictedAction (action e I o) U hU))
    (v : invariantCoordinates (restrictedAction (action e J o') V hV))
    (hu : f u.val = t)
    (hv : f (subframeTransferSection e o o' U V hV h v) = N • t) :
    f (subframeNormalizedCorrection e o o' U hU V hV h hN u v).val = 0 := by
  change f (u.val - (subframeNormalizedTransfer e o o' U hU V hV h hN v).val) = 0
  rw [map_sub, hu, subframeNormalizedTransfer_map e o o' U hU V hV h hN f t v hv,
    sub_self]

variable [Etale p]
open MixedFrames

/-- One representative error controls all original, unscaled embedding equations. -/
theorem subframeNormalizedTransfer_all_branches_iff (ι : J ↪ I)
    (v : invariantCoordinates (restrictedAction (action e J o') V hV)) :
    (∀ κ : J ↪ I,
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartFirst o o' U V).appTop
          (subframeNormalizedTransfer e o o' U hU V hV h hN v).val =
      ((mixedEmbeddingTestOpen e o o' (mixedChartOpen o o' U V).ι κ).ι ≫
        mixedChartSecond o o' U V).appTop v.val) ↔
      subframeTransferSelectionError e o o' U V hV h ι v = 0 := by
  simp only [subframeNormalizedTransfer_branch_iff]
  exact ⟨fun hh ↦ hh ι,
    fun hi κ ↦ subframeTransferSelectionError_zero_all e o o' U hU V hV h ι v hi κ⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
