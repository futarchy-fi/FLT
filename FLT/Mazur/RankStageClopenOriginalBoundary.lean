/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteRelationClopenPrincipalCore
public import FLT.Mazur.RankStageClopenBoundaryOverlap

/-!
# Original chart criteria for exact boundary overlap control

It suffices that the original principal chart domains be clopen on the
order-zero rank support. Their parameters need not be invariant. Pairwise
core closedness is constructed from the actual finite rank relation, giving
unit membership in the original all-order overlap ideal with no stable powers.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance clopenOriginalOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance clopenOriginalOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance clopenOriginalOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)

/-- Closed original principal domains on the rank support give actual closed whole-orbit cores. -/
theorem rankStageCore_isClosed_of_principal_closed (a : Γ(A, ⊤))
    (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
    (h : IsClosed (rankThickeningMap (Over.mk p) n 0 ⁻¹' (A.basicOpen a : Set A))) :
    IsClosed (rankStageCore e n a ha 0 : Set (rankThickening (Over.mk p) n 0)) := by
  let _ := rankStageFirst_finite (p := p) n 0
  apply FiniteRelationAffinePrincipalCore.core_isClosed_of_basicOpen_closed
    (rankStageEquivalence e n 0) _ (rankStagePrincipal_affine n a ha 0)
  change IsClosed ((rankThickening (Over.mk p) n 0).basicOpen
    ((rankThickeningMap (Over.mk p) n 0).appTop a) :
      Set (rankThickening (Over.mk p) n 0))
  rw [← Scheme.preimage_basicOpen_top]
  exact h

variable {S : Scheme.{0}} (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ))
  {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (hclosed : ∀ j,
    IsClosed (rankThickeningMap (Over.mk p) n 0 ⁻¹' (A.basicOpen (c j) : Set A)))

include hclosed in
/-- The actual original-scalar overlap obstruction vanishes on clopen original chart domains. -/
theorem rankStageOriginalBoundaryOverlapIdeal_eq_top_of_principals_closed :
    rankStageOriginalBoundaryOverlapIdeal e n J hJ f hf t c hc = ⊤ := by
  apply rankStageOriginalBoundaryOverlapIdeal_eq_top_of_cores_closed e n J hJ f hf t c hc
  intro j
  apply rankStageCore_isClosed_of_principal_closed e n
  rw [Scheme.basicOpen_mul]
  exact (hclosed j.1).inter (hclosed j.2)

end FLT.Mazur.EquivalenceRelationOrderedFrames
