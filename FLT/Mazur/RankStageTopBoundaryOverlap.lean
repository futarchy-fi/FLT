/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageTopKernelObstruction
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Uniform homogeneous overlap extensions at a top rank

Starting with the original invariant boundary section, geometry annihilates
each constructed overlap obstruction by a norm power. A finite family uses
one exponent at every order, with ordinary compatible global numerators.
The norms differ between overlaps; this does not assert a common original
scalar, unscaled overlap extensions, or splitting by local corrections.
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
local instance topOverlapOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance topOverlapOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance topOverlapOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
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

include hn in
/-- Actual original-boundary overlap errors have all-order norm annihilators at a top rank. -/
theorem rankStageTopBoundaryOverlap_norm_mem_radical (j : ι × ι) :
    r j ∈ (I j).radical :=
  rankStageCompatibleNorm_mem_radical_of_next_empty e n hn (a j) (ha j) J (x j)
    f hf C hC hcover
    (rankStageOriginalBoundaryOverlap_error_zero e n J hJ f hf t c hc j.1 j.2)

include hn in
/-- Finitely many constructed errors have one exponent and ordinary compatible full numerators. -/
theorem exists_rankStageTopBoundaryOverlap_uniform [Finite ι] :
    ∃ (N : ℕ) (w : ∀ _ : ι × ι, ∀ k, rankStageInvariants e n k),
      (∀ j k, w j k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ j k l (h : k ≤ l), rankStageInvariantTransition e n h (w j l) = w j k) ∧
      ∀ j k, rankStageGlobalCoreRestriction e n (a j) (ha j) k (w j k) =
        (rankStageGlobalCoreRestriction e n (a j) (ha j) k ((r j).val k)) ^ N *
          (x j).val k := by
  classical
  let _ := Fintype.ofFinite ι
  have hr (j : ι × ι) :=
    rankStageTopBoundaryOverlap_norm_mem_radical e n hn J hJ f hf t c hc C hC hcover j
  choose m hm using fun j ↦ Ideal.mem_radical_iff.mp (hr j)
  let N := Finset.univ.sup m
  have hN (j : ι × ι) : r j ^ N ∈ I j := by
    have hle : m j ≤ N := Finset.le_sup (Finset.mem_univ j)
    have hh := (I j).mul_mem_left (r j ^ (N - m j)) (hm j)
    simpa only [← pow_add, Nat.sub_add_cancel hle] using hh
  have hw (j : ι × ι) :=
    (mem_rankStageCompatibleNumeratorIdeal e n (a j) (ha j) J (x j) (r j ^ N)).mp (hN j)
  choose w hb ht he using hw
  refine ⟨N, w, hb, ht, fun j k ↦ ?_⟩
  simpa only [Subring.coe_pow, Pi.pow_apply, map_pow] using he j k

end FLT.Mazur.EquivalenceRelationOrderedFrames
