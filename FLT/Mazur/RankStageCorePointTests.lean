/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryCoefficients
public import FLT.Mazur.IdealSheafClosedCoreTests
public import FLT.Mazur.RelativeRankStageSectionDetection

/-!
# Full infinitesimal point tests inside coherent original cores

Every infinitesimal test at a covered original point factors through a
finite order of that same core. Pulling the core back to the unchanged
coefficient scheme therefore detects its full local section germ.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeInfinitesimalPointDetection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance corePointOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance corePointOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance corePointOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤))
  (h : ∀ k, rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤
    rankStageCore e n a ha k)
  (g : B ⟶ A) (x : B) (hx : g x ∈ exactRank (Over.mk p) n) (hb : g x ∈ A.basicOpen b)
attribute [local irreducible] rankStageCore rankStageCoreOriginalMap

include h hx hb in
/-- An actual unreduced point test factors through a finite order of its selected core. -/
theorem pointThickening_core_factor (k : ℕ) :
    ∃ (order : ℕ)
      (u : pointThickening B x k ⟶ pullback (rankStageCoreOriginalMap e n a ha order) g),
      u ≫ pullback.snd _ _ = pointThickeningMap B x k := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨order, u, hu⟩ := infinitesimalPoint_rank_factor (Over.mk p) g x n k hx
  let v := u ≫ pullback.fst (rankThickeningMap (Over.mk p) n order) g
  have hv : v ≫ rankThickeningMap (Over.mk p) n order = pointThickeningMap B x k ≫ g := by
    rw [show v = u ≫ pullback.fst _ _ from rfl, Category.assoc, pullback.condition,
      ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ g) hu
  have hc : ⊤ ≤ v ⁻¹ᵁ rankStageCore e n a ha order := by
    intro y _
    apply h order
    change rankThickeningMap (Over.mk p) n order (v y) ∈ A.basicOpen b
    rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, pointThickeningMap_apply]
    exact hb
  let z := IdealSheafClosedCoreTests.openLift (rankStageCore e n a ha order) v hc
  have hz : z ≫ rankStageCoreOriginalMap e n a ha order = pointThickeningMap B x k ≫ g := by
    rw [rankStageCoreOriginalMap, ← Category.assoc]
    exact (congrArg (fun w ↦ w ≫ rankThickeningMap (Over.mk p) n order)
      (IdealSheafClosedCoreTests.openLift_inclusion _ v hc)).trans hv
  exact ⟨order, pullback.lift z (pointThickeningMap B x k) hz, pullback.lift_snd _ _ _⟩

include h hx hb in
/-- Vanishing on all orders of one core kills every infinitesimal test at its covered point. -/
theorem pointThickening_zero_of_core_orders (s : Γ(B, ⊤))
    (hs : ∀ order, (pullback.snd (rankStageCoreOriginalMap e n a ha order) g).appTop s = 0)
    (k : ℕ) : (pointThickeningMap B x k).appTop s = 0 := by
  obtain ⟨order, u, hu⟩ := pointThickening_core_factor e n a ha b h g x hx hb k
  rw [← hu, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, hs, map_zero]

include h hx hb in
/-- Coherent core orders detect the full original germ, including its nilpotents. -/
theorem germ_zero_of_core_orders [IsLocallyNoetherian B] (s : Γ(B, ⊤))
    (hs : ∀ order, (pullback.snd (rankStageCoreOriginalMap e n a ha order) g).appTop s = 0) :
    B.presheaf.germ ⊤ x trivial s = 0 :=
  germ_eq_zero B x s (pointThickening_zero_of_core_orders e n a ha b h g x hx hb s hs)

end FLT.Mazur.EquivalenceRelationOrderedFrames
