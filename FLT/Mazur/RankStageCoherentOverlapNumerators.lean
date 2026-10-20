/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageRescaledGlobalKernelTowers
public import FLT.Mazur.RankStageFiniteGlobalOverlapNumerators

/-!
# Coherent global numerators of all actual finite-cover overlap errors

Independent compatible towers of full boundary lifts on the finite rank-core
cover construct global homogeneous overlap numerators. One monotone exponent
sequence serves every pair of cores. All pairs of closed order transitions
satisfy an exact rescaled equation, with the unchanged global norm parameters.
These are still scaled errors, not unscaled corrections or algebraized sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance coherentNumOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coherentNumOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coherentNumOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (ha : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (ha c) k) = ⊤)
  (J : A.IdealSheafData)
local notation "a" c:max => (c).val.1
local notation "hab" c:max d:max => rankStageProduct_domain n (a c) (a d) (ha c)
local notation "U" c:max d:max k:max => rankStageCore e n (a c * a d) (hab c d) k
local notation "r" c:max d:max k:max => rankStageNormParameter e n C ha hc (a c * a d) k
attribute [local irreducible] rankStageCore rankStageNormParameter rankStageInvariantOverlapError
  rankStageCoreRestriction rankStageCoreBoundaryIdeal rankStageCoreOriginalBoundaryMap
  rankStageInvariantTransition rankStageGlobalCoreRestriction rankStageGlobalBoundaryKernel

/-- The whole finite-cover error family has one coherent rescaled global numerator tower. -/
theorem exists_rankStage_coherent_overlap_numerators
    (v : ∀ (c : C) k, rankStageCoreInvariants e n (a c) (ha c) k)
    (t : Γ(J.subscheme, ⊤))
    (hv : ∀ (c : C) k,
      (rankStageCoreBoundaryIdeal e n (a c) (ha c) J k).subschemeι.appTop (v c k).val =
        (rankStageCoreOriginalBoundaryMap e n (a c) (ha c) J k).appTop t)
    (ht : ∀ (c : C) k l (h : k ≤ l),
      rankStageCoreRestriction e n (a c) (ha c) h (v c l) = v c k) :
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
  let err (j : C × C) (k : ℕ) :
      rankStageCoreInvariants e n (a j.1 * a j.2) (hab j.1 j.2) k :=
    rankStageInvariantOverlapError e n (a j.1) (a j.2) (ha j.1) (ha j.2) k
      (v j.1 k) (v j.2 k)
  have he (j : C × C) (k l : ℕ) (h : k ≤ l) :
      rankStageCoreRestriction e n (a j.1 * a j.2) (hab j.1 j.2) h (err j l) = err j k := by
    exact (rankStageInvariantOverlapError_transition e n (a j.1) (a j.2)
      (ha j.1) (ha j.2) h (v j.1 l) (v j.2 l)).trans
        (congrArg₂ (rankStageInvariantOverlapError e n (a j.1) (a j.2)
          (ha j.1) (ha j.2) k) (ht j.1 k l h) (ht j.2 k l h))
  obtain ⟨N, w, hN, hw, hl, hh⟩ := exists_rankStage_rescaled_global_kernel_towers e n C ha hc J
    (fun j : C × C ↦ a j.1 * a j.2) (fun j ↦ hab j.1 j.2) err
    (fun j k ↦ rankStageInvariantOverlapError_boundary_zero e n (a j.1) (a j.2)
      (ha j.1) (ha j.2) J k (v j.1 k) (v j.2 k) t (hv j.1 k) (hv j.2 k)) he
  refine ⟨N, fun k c d ↦ w k (c, d), hN, ?_, ?_, ?_⟩
  · intro k c d
    exact (mem_rankStageGlobalBoundaryKernel e n J k _).mp (hw k (c, d))
  · intro k c d
    have h := congrArg Subtype.val (hl k (c, d))
    simpa only [rankStageGlobalCoreRestriction_val, Subring.coe_mul, Subring.coe_pow] using h
  · intro k l h c d
    have hh' := congrArg Subtype.val (hh k l h (c, d))
    simpa only [rankStageInvariantTransition_val, Subring.coe_mul, Subring.coe_pow] using hh'

end FLT.Mazur.EquivalenceRelationOrderedFrames
