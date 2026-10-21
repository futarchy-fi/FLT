/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryUniformRelationIdeal
public import FLT.Mazur.RankStageCoreCorrectionSpace

/-!
# Uniform full-rank corrections from original relation equations

One test-ideal power, chosen before the boundary or the rank, annihilates
every whole-core correction class whose original raw numerator solves the
same relation open. This uses original lift numerators in the proved forward
direction only. No finite full correction cokernel is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance uniformRelationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance uniformRelationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance uniformRelationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCoreCorrectionIdeal

/-- One original ideal power corrects every rank and whole-core family using the solved open. -/
theorem exists_pow_le_all_rankStageCorrectionIdeals_of_relation_open
    (O : D.Opens) (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : Q ≤ scalarAvoidanceIdeal (p.appTop.hom.comp (compatibleFunctions p q).subtype) O) :
    ∃ N : ℕ, ∀ (J : A.IdealSheafData) (a : Γ(A, ⊤)),
      O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a) →
      ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
        (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
        (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
        (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
          ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop
            (J.subschemeι.appTop a)) →
        Q ^ N ≤ rankStageCoreCorrectionIdeal e n c hc J v := by
  let _ : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian p
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ : IsNoetherian D := ⟨⟩
  obtain ⟨N, hN⟩ := exists_pow_le_originalRelationMultiplierIdeal O Q hfg hQ
  refine ⟨N, fun J a ha n _ c hc v hv ↦ ?_⟩
  apply le_trans _ (originalBoundaryLiftIdeal_le_correctionIdeal J
    (J.subschemeι.appTop a) e n c hc v hv)
  intro s hs
  exact originalRelationMultiplier_mem_liftIdeal O s (hN hs) J a ha

end FLT.Mazur.EquivalenceRelationOrderedFrames
