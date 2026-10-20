/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageStableKernelObstruction
public import FLT.Mazur.RankStratumClopenStabilization
public import FLT.Mazur.RankStageOriginalScalarAnnihilation

/-!
# All-order annihilation below a closed higher-frame locus

Higher frames may be present: closedness of their image gives geometric
stabilization on the full rank stratum. Both the constructed norm and, for
invariant principal domains, the unchanged original scalar annihilate the
actual compatible homogeneous obstruction by one ordinary power.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance clopenKernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance clopenKernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance clopenKernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (hn : IsClosed (rankImageOpen (Over.mk p) (n + 1) : Set A))
  (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (x : rankStageCompatibleCoreInvariants e n a ha)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
  (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageCompatibleNorm rankStageCompatibleNumeratorIdeal

include hn hf hx in
/-- Closed higher-frame geometry places the norm in the actual all-order obstruction radical. -/
theorem rankStageCompatibleNorm_mem_radical_of_next_closed :
    rankStageCompatibleNorm e n a C hC hc ∈
      (rankStageCompatibleNumeratorIdeal e n a ha J x).radical := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_closed (Over.mk p) n hn
  exact rankStageCompatibleNorm_mem_radical_of_stable e n K hK a ha J x f hf C hC hc hx

include hn hf hx in
/-- One exponent extends the entire homogeneous tower below a closed higher-frame locus. -/
theorem exists_rankStage_uniform_kernel_tower_of_next_closed :
    ∃ (N : ℕ) (w : ∀ k, rankStageInvariants e n k),
      (∀ k, w k ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ k l (h : k ≤ l), rankStageInvariantTransition e n h (w l) = w k) ∧
      ∀ k, rankStageGlobalCoreRestriction e n a ha k (w k) =
        (rankStageGlobalCoreRestriction e n a ha k
          (rankStageNormParameter e n C hC hc a k)) ^ N * x.val k :=
  (rankStageCompatibleNorm_mem_radical_iff e n a ha J x C hC hc).mp
    (rankStageCompatibleNorm_mem_radical_of_next_closed e n hn a ha J x f hf C hC hc hx)

include hn hf in
/-- For invariant principal domains the annihilator stays in the original full-source ring. -/
theorem rankStageOriginalScalar_mem_radical_of_next_closed
    (s : SchemeEffectiveEpiSections.compatibleFunctions p q)
    (hs : A.basicOpen s.val ≤ rankImageOpen (Over.mk p) n)
    (y : rankStageCompatibleCoreInvariants e n s.val hs)
    (hy : ∀ k, (rankStageCoreBoundaryIdeal e n s.val hs J k).subschemeι.appTop
      (y.val k).val = 0) :
    s ∈ (rankStageOriginalNumeratorIdeal e n s.val hs J y).radical := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_closed (Over.mk p) n hn
  exact rankStageOriginalScalar_mem_radical_of_stable e n s hs J y f hf hy K hK

end FLT.Mazur.EquivalenceRelationOrderedFrames
