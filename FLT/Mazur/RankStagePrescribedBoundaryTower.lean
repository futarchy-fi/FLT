/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStagePrescribedBoundaryLifting

/-!
# Compatible rank-stage lifts with every full boundary value prescribed

Every compatible sequence of full boundary invariants has a compatible
sequence of full invariant lifts on the same affine domains. A specified
initial lift is retained. This is an infinitesimal tower, not algebraization
or descent to the unchanged original source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance prescribedTowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance prescribedTowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance prescribedTowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "C" => rankStageCoreInvariants e n a ha
local notation "B" => rankStageCoreBoundaryInvariants e n a ha J hJ
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J
local notation "ρ" => rankStageCoreRestriction e n a ha

attribute [local irreducible] rankStageCore rankStageCoreRestriction rankStageCoreMap
  rankStageFirst rankStageSecond rankThickening
  rankStageCoreBoundaryIdeal rankStageCoreBoundaryMap

include hf in
/-- All higher boundary values can be prescribed while retaining a chosen initial lift. -/
theorem exists_rankStage_prescribed_boundary_tower (t : ∀ k : ℕ, B k)
    (ht : ∀ k, (rankStageCoreBoundaryMap e n a ha J (Nat.le_succ k)).appTop (t (k + 1)).val =
        (t k).val)
    (z : C 0) (hz : (I 0).subschemeι.appTop z.val = (t 0).val) :
    ∃ v : ∀ k : ℕ, C k, v 0 = z ∧ (∀ k, (I k).subschemeι.appTop (v k).val = (t k).val) ∧
      ∀ k l (h : k ≤ l), ρ h (v l) = v k := by
  let T (k : ℕ) := {s : C k // (I k).subschemeι.appTop s.val = (t k).val}
  have next (k : ℕ) (s : T k) : ∃ w : C (k + 1), ρ (Nat.le_succ k) w = s.val ∧
      (I (k + 1)).subschemeι.appTop w.val = (t (k + 1)).val := by
    apply exists_rankStage_prescribed_boundary_lift e n a ha J hJ f hf
    exact s.property.trans (ht k).symm
  let lift (k : ℕ) (s : T k) : T (k + 1) := ⟨(next k s).choose, (next k s).choose_spec.2⟩
  let w : ∀ k : ℕ, T k := Nat.rec ⟨z, hz⟩ (fun k s ↦ lift k s)
  let v (k : ℕ) : C k := (w k).val
  have step (k : ℕ) : ρ (Nat.le_succ k) (v (k + 1)) = v k := (next k (w k)).choose_spec.1
  refine ⟨v, rfl, fun k ↦ (w k).property, ?_⟩
  intro k l h
  induction l, h using Nat.le_induction with
  | base => exact rankStageCoreRestriction_refl e n a ha k (v k)
  | succ l h ih =>
    rw [← rankStageCoreRestriction_comp e n a ha h (Nat.le_succ l), step]
    exact ih

end FLT.Mazur.EquivalenceRelationOrderedFrames
