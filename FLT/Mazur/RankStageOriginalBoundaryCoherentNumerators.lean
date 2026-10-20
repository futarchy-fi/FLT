/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoherentOverlapNumerators
public import FLT.Mazur.RankStageOriginalBoundaryTower

/-!
# Constructed coherent overlap numerators for original boundary data

One full invariant section on the unchanged original boundary constructs the
local compatible lifts and their coherent global homogeneous error numerators.
No local towers or overlap corrections are supplied as extra hypotheses. The
norm exponents may still grow, and the stage sections are not algebraized.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance originalCoherentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance originalCoherentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance originalCoherentOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (ha c) k) = ⊤)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
local notation "a" c:max => (c).val.1
local notation "hab" c:max d:max => rankStageProduct_domain n (a c) (a d) (ha c)
local notation "U" c:max d:max k:max => rankStageCore e n (a c * a d) (hab c d) k
local notation "r" c:max d:max k:max => rankStageNormParameter e n C ha hc (a c * a d) k
attribute [local irreducible] rankStageCore rankStageNormParameter rankStageInvariantOverlapError

include hf in
/-- Original boundary data construct both compatible local lifts and coherent global errors. -/
theorem exists_rankStage_original_boundary_coherent_numerators
    (t : compatibleFunctions (pullback.snd p J.subschemeι)
      (InvariantIdealRelation.snd J p q hJ)) :
    ∃ v : ∀ (c : C) k, rankStageCoreInvariants e n (a c) (ha c) k,
      (∀ (c : C) k,
        (rankStageCoreBoundaryIdeal e n (a c) (ha c) J k).subschemeι.appTop (v c k).val =
          (rankStageCoreOriginalBoundaryMap e n (a c) (ha c) J k).appTop t.val) ∧
      (∀ (c : C) k l (h : k ≤ l),
        rankStageCoreRestriction e n (a c) (ha c) h (v c l) = v c k) ∧
    ∃ (N : ℕ → ℕ) (w : ∀ k, C → C → rankStageInvariants e n k), Monotone N ∧
      (∀ k c d, (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop
        (w k c d).val = 0) ∧
      (∀ k c d, (U c d k).ι.appTop (w k c d).val =
        ((U c d k).ι.appTop (r c d k).val) ^ N k *
          (rankStageInvariantOverlapError e n (a c) (a d) (ha c) (ha d) k
            (v c k) (v d k)).val) ∧
      ∀ k l (h : k ≤ l) c d,
        (rankStageTransition (Over.mk p) n h).appTop (w l c d).val =
          (r c d k).val ^ (N l - N k) * (w k c d).val := by
  classical
  have hex (c : C) := exists_rankStage_original_boundary_tower e n (a c) (ha c) J hJ f hf t
  choose v hv ht using hex
  exact ⟨v, hv, ht, exists_rankStage_coherent_overlap_numerators e n C ha hc J v t.val hv ht⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
