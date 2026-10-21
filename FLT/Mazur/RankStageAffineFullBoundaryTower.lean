/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFullBoundaryLifting

/-!
# Global prescribed boundary towers on affine rank thickenings

Successive simultaneous lifts construct a compatible tower on the entire
rank support. The full boundary at every order is prescribed in advance.
Affineness is explicit; core closedness and stabilization are not needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fullTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fullTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fullTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  [∀ k, IsAffine (rankThickening (Over.mk p) n k)]
local notation "I" k:max => rankStageBoundaryIdeal (p := p) n k J
local notation "B" k:max => rankStageFullBoundaryInvariants e n J hJ k
local notation "C" k:max => rankStageInvariants e n k
local notation "ρ" => rankStageInvariantTransition e n
attribute [local irreducible] rankStageFirst rankStageSecond rankStageInvariantTransition
  rankStageFullBoundaryTransition rankStageFullOriginalBoundaryMap

include hf in
/-- Retain a specified initial lift while prescribing every higher full boundary value. -/
theorem exists_rankStage_affine_full_prescribed_tower (t : ∀ k, B k)
    (ht : ∀ k, (rankStageFullBoundaryTransition (p := p) n J (Nat.le_succ k)).appTop
      (t (k + 1)).val = (t k).val)
    (z : C 0) (hz : (I 0).subschemeι.appTop z.val = (t 0).val) :
    ∃ v : ∀ k, C k, v 0 = z ∧
      (∀ k, (I k).subschemeι.appTop (v k).val = (t k).val) ∧
      ∀ k l (h : k ≤ l), ρ h (v l) = v k := by
  let T (k : ℕ) := {s : C k // (I k).subschemeι.appTop s.val = (t k).val}
  have next (k : ℕ) (s : T k) : ∃ w : C (k + 1), ρ (Nat.le_succ k) w = s.val ∧
      (I (k + 1)).subschemeι.appTop w.val = (t (k + 1)).val := by
    apply exists_rankStage_full_prescribed_boundary_lift e n J hJ f hf
    exact s.property.trans (ht k).symm
  let lift (k : ℕ) (s : T k) : T (k + 1) := ⟨(next k s).choose, (next k s).choose_spec.2⟩
  let w : ∀ k, T k := Nat.rec ⟨z, hz⟩ (fun k s ↦ lift k s)
  let v (k : ℕ) : C k := (w k).val
  have step (k : ℕ) : ρ (Nat.le_succ k) (v (k + 1)) = v k := (next k (w k)).choose_spec.1
  refine ⟨v, rfl, fun k ↦ (w k).property, ?_⟩
  intro k l h
  induction l, h using Nat.le_induction with
  | base =>
    apply Subtype.ext
    rw [rankStageInvariantTransition_val]
    have he : rankStageTransition (Over.mk p) n (le_refl k) = 𝟙 _ := by
      apply (cancel_mono (rankThickeningMap (Over.mk p) n k)).mp
      rw [rankStageTransition_map, Category.id_comp]
    rw [he]
    rfl
  | succ l h ih =>
    have he := congrArg (fun g : C (l + 1) →+* C k ↦ g (v (l + 1)))
      (rankStageInvariantTransition_comp e n h (Nat.le_succ l))
    exact he.symm.trans ((congrArg (ρ h) (step l)).trans ih)

include hf in
/-- One original boundary invariant has a global full tower on affine rank thickenings. -/
theorem exists_rankStage_affine_full_original_boundary_tower
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ v : ∀ k, C k,
      (∀ k l (h : k ≤ l), ρ h (v l) = v k) ∧
      ∀ k, (I k).subschemeι.appTop (v k).val =
        (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t.val := by
  let u (k : ℕ) := rankStageFullBoundaryRestriction e n J hJ k t
  obtain ⟨z, hz⟩ := exists_rankStage_full_initial_boundary_lift e n J hJ f hf 0 (u 0)
  obtain ⟨v, _, hb, hc⟩ := exists_rankStage_affine_full_prescribed_tower e n J hJ f hf u
    (fun k ↦ rankStageFullBoundaryRestriction_compatible e n J hJ (Nat.le_succ k) t) z hz
  exact ⟨v, hc, hb⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
