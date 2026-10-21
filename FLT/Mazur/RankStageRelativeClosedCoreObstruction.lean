/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStratumRelativeClosedStabilization
public import FLT.Mazur.RankStageOriginalCoreAnnihilation

/-!
# Original-scalar obstruction control with relatively closed higher ranks

Higher-frame loci may fail to be closed in the original source. Closedness
inside the unchanged current rank open constructs full ideal stabilization.
Original invariant principal parameters then annihilate the entire compatible
homogeneous obstruction. Arbitrary parameters use the explicit core interface.
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
local instance relativeClosedOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance relativeClosedOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance relativeClosedOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)
  (hn : IsClosed ((rankImageOpen (Over.mk p) n).ι ⁻¹'
    (rankImageOpen (Over.mk p) (n + 1) : Set A)))
  (J : A.IdealSheafData) {S : Scheme.{0}} [IsAffine S] (f : A ⟶ S)
  (hf : p ≫ f = q ≫ f) [IsSeparated f]
attribute [local irreducible] rankStageCore rankStageOriginalInvariantRestriction

include hn hf in
/-- Relative rank closedness controls arbitrary cores defined by unchanged original scalars. -/
theorem rankStageOriginalCoreScalar_mem_radical_of_next_relatively_closed
    (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
    (s : compatibleFunctions p q) (x : rankStageCompatibleCoreInvariants e n a ha)
    (hx : ∀ k, (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop (x.val k).val = 0)
    (hs : ∀ k, rankStageCore e n a ha k = (rankThickening (Over.mk p) n k).basicOpen
      (rankStageOriginalInvariantRestriction e n k s).val) :
    s ∈ (rankStageOriginalNumeratorIdeal e n a ha J x).radical := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_stable_of_next_relatively_closed (Over.mk p) n hn
  exact rankStageOriginalCoreScalar_mem_radical_of_stable e n a ha J x f hf s hx K hK (hs K)

include hn hf in
/-- Invariant original domains need no further core hypothesis or global finiteness. -/
theorem rankStageOriginalScalar_mem_radical_of_next_relatively_closed
    (s : compatibleFunctions p q) (hs : A.basicOpen s.val ≤ rankImageOpen (Over.mk p) n)
    (x : rankStageCompatibleCoreInvariants e n s.val hs)
    (hx : ∀ k, (rankStageCoreBoundaryIdeal e n s.val hs J k).subschemeι.appTop
      (x.val k).val = 0) :
    s ∈ (rankStageOriginalNumeratorIdeal e n s.val hs J x).radical := by
  exact rankStageOriginalCoreScalar_mem_radical_of_next_relatively_closed e n hn J f hf
    s.val hs s x hx (rankStageCore_eq_basicOpen_original e n s hs)

end FLT.Mazur.EquivalenceRelationOrderedFrames
