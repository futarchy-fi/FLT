/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoherentAffineCores
public import FLT.Mazur.RankStageInvariantTransitions
public import FLT.Mazur.FiniteEtaleInvariantDomainCoefficients

/-!
# Full invariant coefficient maps on coherent affine rank domains

The rings use one fixed domain at each order. Actual scheme restriction gives
composable maps, and every transition is surjective by the full finite etale
relation theorem. The entire original rank stage need not be affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coreCoeffOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coreCoeffOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coreCoeffOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
local notation "U" => rankStageCore e n a ha
local notation "hU" => rankStageCore_invariant e n a ha

/-- A fixed full endpoint equalizer on the chosen affine domain at each rank order. -/
abbrev rankStageCoreInvariants (k : ℕ) :=
  compatibleFunctions ((rankStageFirst (p := p) n k).resLE (U k) _ le_rfl)
    ((rankStageSecond e n k).resLE (U k) _ (hU k).le)

/-- The actual source map between coordinated affine rank domains. -/
def rankStageCoreMap {k l : ℕ} (h : k ≤ l) : (U k).toScheme ⟶ (U l).toScheme :=
  (rankStageTransition (Over.mk p) n h).resLE _ _ (rankStageCore_preimage e n a ha h).ge

/-- The domain transition retains the original infinitesimal source map. -/
@[reassoc]
theorem rankStageCoreMap_inclusion {k l : ℕ} (h : k ≤ l) :
    rankStageCoreMap e n a ha h ≫ (U l).ι =
      (U k).ι ≫ rankStageTransition (Over.mk p) n h := Scheme.Hom.resLE_comp_ι _ _

/-- Named affine domain maps compose before any passage to coefficients. -/
@[reassoc]
theorem rankStageCoreMap_comp {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m) :
    rankStageCoreMap e n a ha h ≫ rankStageCoreMap e n a ha h' =
      rankStageCoreMap e n a ha (h.trans h') := by
  apply (cancel_mono (U m).ι).mp
  rw [Category.assoc, rankStageCoreMap_inclusion, rankStageCoreMap_inclusion_assoc,
    rankStageTransition_comp, rankStageCoreMap_inclusion]

/-- Pullback of the entire invariant ring on the chosen affine domains. -/
def rankStageCoreRestriction {k l : ℕ} (h : k ≤ l) :
    rankStageCoreInvariants e n a ha l →+* rankStageCoreInvariants e n a ha k :=
  FiniteEtaleInvariantDomainCoefficients.restriction _ _ _ _ (rankStageTransition (Over.mk p) n h)
    (rankStageRelationTransition (p := p) n h) (rankStageRelationTransition_isPullback n h)
    (rankStageRelationTransition_second e n h) (U l) (U k) (hU l) (hU k)
    (rankStageCore_preimage e n a ha h).symm

/-- The full invariant map is actual restriction of the original source function. -/
theorem rankStageCoreRestriction_val {k l : ℕ} (h : k ≤ l)
    (s : rankStageCoreInvariants e n a ha l) :
    (rankStageCoreRestriction e n a ha h s).val =
      (rankStageCoreMap e n a ha h).appTop s.val := rfl

/-- All coefficient paths through the actual named domains agree. -/
theorem rankStageCoreRestriction_comp {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m)
    (s : rankStageCoreInvariants e n a ha m) :
    rankStageCoreRestriction e n a ha h (rankStageCoreRestriction e n a ha h' s) =
      rankStageCoreRestriction e n a ha (h.trans h') s := by
  apply Subtype.ext
  simp only [rankStageCoreRestriction_val]
  change (rankStageCoreMap e n a ha h ≫ rankStageCoreMap e n a ha h').appTop s.val = _
  rw [rankStageCoreMap_comp]

variable {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]

include hf in
/-- Full invariant lifts exist across every order on these actual affine domains. -/
theorem rankStageCoreRestriction_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (rankStageCoreRestriction e n a ha h) := by
  let _ := rankStageFirst_finite (p := p) n l
  let b := rankThickeningMap (Over.mk p) n l
  let _ : IsSeparated (b ≫ f) := by
    dsimp [b, rankThickeningMap]
    infer_instance
  have H : rankStageFirst (p := p) n l ≫ (b ≫ f) = rankStageSecond e n l ≫ (b ≫ f) := by
    rw [← Category.assoc, ← (rankStageFirst_isPullback (p := p) n l).w,
      Category.assoc, hf, ← Category.assoc, ← rankStageSecond_map, Category.assoc]
  exact FiniteEtaleInvariantDomainCoefficients.restriction_surjective _ _ _ _ _ _
    (rankStageRelationTransition_isPullback n h) (rankStageRelationTransition_second e n h)
    (U l) (U k) (hU l) (hU k) (rankStageCore_preimage e n a ha h).symm
    (b ≫ f) H (rankStageEquivalence e n l) (rankStageCore_affine e n a ha l)

end FLT.Mazur.EquivalenceRelationOrderedFrames
