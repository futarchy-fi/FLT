/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreRelationPullback
public import FLT.Mazur.RankStageFiniteCoreDetection

/-!
# Original invariant membership detected by all coherent core orders

An existing original section belongs to the full invariant ring exactly when
its restrictions do so on every selected core order. This constructs invariant
coefficients from full section candidates without assuming their invariance.
It does not construct a full section from an arbitrary formal tower.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance invariantDetectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance invariantDetectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance invariantDetectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap

/-- The original full invariant coefficient restricts to every entire core relation. -/
theorem original_invariant_mem_core (n : ℕ) (a : Γ(A, ⊤))
    (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
    (s : Γ(A, ⊤)) (hs : s ∈ compatibleFunctions p q) :
    (rankStageCoreOriginalMap e n a ha k).appTop s ∈ rankStageCoreInvariants e n a ha k := by
  have he := congrArg (rankStageCoreOriginalArrow e n a ha k).appTop hs
  change (rankStageCoreOriginalArrow e n a ha k ≫ p).appTop s =
    (rankStageCoreOriginalArrow e n a ha k ≫ q).appTop s at he
  rw [rankStageCoreOriginalArrow_first, rankStageCoreOriginalArrow_second] at he
  exact he

variable {ι : Type}
  (n : ι → ℕ) (a b : ι → Γ(A, ⊤))
  (ha : ∀ i, A.basicOpen (a i) ≤ rankImageOpen (Over.mk p) (n i))
  (h : ∀ i k, rankThickeningMap (Over.mk p) (n i) k ⁻¹ᵁ A.basicOpen (b i) ≤
    rankStageCore e (n i) (a i) (ha i) k)
  (hcover : ∀ x : A, ∃ i, x ∈ exactRank (Over.mk p) (n i) ∧ x ∈ A.basicOpen (b i))

include h hcover in
/-- Full core membership at all orders forces the original entire relation equation. -/
theorem original_invariant_of_core_orders (s : Γ(A, ⊤))
    (hs : ∀ i k, (rankStageCoreOriginalMap e (n i) (a i) (ha i) k).appTop s ∈
      rankStageCoreInvariants e (n i) (a i) (ha i) k) :
    s ∈ compatibleFunctions p q := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian p
  change p.appTop s = q.appTop s
  apply section_eq_of_selected_core_orders e p n a b ha h (fun z ↦ hcover (p z))
  intro i k
  let f := rankStageCoreOriginalMap e (n i) (a i) (ha i) k
  obtain ⟨u', hu', hv⟩ := rankStageCore_original_invariant_test e (n i) (a i) (ha i) k
    (pullback.fst f p) (pullback.snd f p) pullback.condition.symm ⟨f.appTop s, hs i k⟩
  change (pullback.snd f p ≫ p).appTop s = (pullback.snd f p ≫ q).appTop s
  rw [← pullback.condition, hu']
  exact hv

include h hcover in
/-- This is equality with the actual invariant subring, retaining nonreduced coefficients. -/
theorem original_invariant_iff_core_orders (s : Γ(A, ⊤)) :
    s ∈ compatibleFunctions p q ↔
      ∀ i k, (rankStageCoreOriginalMap e (n i) (a i) (ha i) k).appTop s ∈
        rankStageCoreInvariants e (n i) (a i) (ha i) k :=
  ⟨fun hs i k ↦ original_invariant_mem_core e (n i) (a i) (ha i) k s hs,
    original_invariant_of_core_orders e n a b ha h hcover s⟩

/-- A full section candidate with invariant core values gives an actual original invariant. -/
def originalInvariantOfCoreOrders (s : Γ(A, ⊤))
    (hs : ∀ i k, (rankStageCoreOriginalMap e (n i) (a i) (ha i) k).appTop s ∈
      rankStageCoreInvariants e (n i) (a i) (ha i) k) : compatibleFunctions p q :=
  ⟨s, original_invariant_of_core_orders e n a b ha h hcover s hs⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
