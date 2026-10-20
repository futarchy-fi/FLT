/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageTopBoundaryOverlap
public import FLT.Mazur.RankOpenHomogeneousFamilies

/-!
# Original rank-open numerators for constructed boundary overlaps

The uniform homogeneous overlap towers algebraize simultaneously on the
unchanged original rank-image open, retaining all boundary and order equations.
This does not extend across its complement or split the overlap cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance openOverlapOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance openOverlapOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance openOverlapOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
omit [LocallyQuasiFinite p] in
private theorem algebraize_overlap_equations {κ η : Type*} (m : ℕ)
    (hm : rankImageOpen (Over.mk p) (m + 1) = ⊥) (B : A.IdealSheafData)
    (P : κ → (∀ _ : η, ∀ k, rankStageInvariants e m k) → Prop)
    (h : ∃ N w, (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e m B k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e m h (w j l) = w j k) ∧
      P N w) :
    ∃ (N : κ) (z : η → compatibleFunctions (rankOpenFirst (p := p) m) (rankOpenSecond e m)),
      (∀ j, (B.comap (Scheme.Opens.ι (rankImageOpen (Over.mk p) m))).subschemeι.appTop
        (z j).val = 0) ∧ P N (fun j k ↦ rankOpenInvariantRestriction e m k (z j)) := by
  obtain ⟨N, w, hb, ht, he⟩ := h
  obtain ⟨z, hzB, hzW⟩ := exists_rankOpen_homogeneous_family e m hm B w hb ht
  refine ⟨N, z, hzB, ?_⟩
  have hzw : (fun j k ↦ rankOpenInvariantRestriction e m k (z j)) = w :=
    funext fun j ↦ funext (hzW j)
  rw [hzw]
  exact he

variable (n : ℕ) (hn : rankImageOpen (Over.mk p) (n + 1) = ⊥)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ d : C, A.basicOpen d.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hcover : ∀ k, (⨆ d : C, rankStageCore e n d.val.1 (hC d) k) = ⊤)
local notation "v" j:max => rankStageChosenBoundaryCoreTower e n (c j) (hc j) J hJ f hf t
local notation "a" j:max => c j.1 * c j.2
local notation "ha" j:max => rankStageProduct_domain n (c j.1) (c j.2) (hc j.1)
local notation "x" j:max => rankStageCompatibleOverlapError e n (c j.1) (c j.2)
  (hc j.1) (hc j.2) (v j.1) (v j.2)
local notation "r" j:max => rankStageCompatibleNorm e n (a j) C hC hcover
local notation "I" j:max => rankStageCompatibleNumeratorIdeal e n (a j) (ha j) J (x j)
attribute [local irreducible] rankStageCore rankStageCompatibleNorm
  rankStageCompatibleNumeratorIdeal rankStageChosenBoundaryCoreTower
  rankStageCompatibleOverlapError rankStageGlobalCoreRestriction rankStageInvariantTransition

attribute [local irreducible] rankImageOpen rankStratumIdeal rankOpenFirst rankOpenSecond
  rankStageGlobalBoundaryKernel rankStageFirst rankStageSecond rankThickening
  rankStageNormParameter Scheme.basicOpen rankOpenInvariantRestriction

include hn in
/-- Actual boundary overlap errors have one exponent and full original rank-open numerators. -/
theorem exists_rankOpenTopBoundary_uniform_numerators [Finite ι] :
    ∃ (N : ℕ) (z : ι × ι →
      compatibleFunctions (rankOpenFirst (p := p) n) (rankOpenSecond e n)),
      (∀ j, (J.comap (Scheme.Opens.ι (rankImageOpen (Over.mk p) n))).subschemeι.appTop
        (z j).val = 0) ∧
      ∀ j k, rankStageGlobalCoreRestriction e n (a j) (ha j) k
          (rankOpenInvariantRestriction e n k (z j)) =
        (rankStageGlobalCoreRestriction e n (a j) (ha j) k ((r j).val k)) ^ N *
          (x j).val k := by
  apply algebraize_overlap_equations e (κ := ℕ) (η := ι × ι) n hn J
    (fun N w ↦ ∀ (j : ι × ι) k,
    rankStageGlobalCoreRestriction e n (a j) (ha j) k (w j k) =
      (rankStageGlobalCoreRestriction e n (a j) (ha j) k ((r j).val k)) ^ N *
        (x j).val k)
  exact exists_rankStageTopBoundaryOverlap_uniform e n hn J hJ f hf t c hc C hC hcover

end FLT.Mazur.EquivalenceRelationOrderedFrames
