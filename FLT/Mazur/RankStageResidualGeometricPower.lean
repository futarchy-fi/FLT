/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualIdeal
public import FLT.Mazur.RankStageCoreCorrectionSpace

/-!
# Residual geometric powers for every rank correction

A test only on the residual intersection gives one original scalar ideal
power that corrects every rank and every compatible whole-core boundary lift.
The exponent is chosen on the original source before any rank or core family.
An empty residual intersection gives unscaled vanishing of all these classes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeOpenEnvelope
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance residualPowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance residualPowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance residualPowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "σ" => Subring.subtype (compatibleFunctions p q)
attribute [local irreducible] rankStageCoreCorrectionIdeal rankStageCoreCorrectionObstruction

include hf in
/-- One ideal exponent works for all full-boundary rank corrections from residual geometry. -/
theorem exists_pow_le_all_rankStageCoreCorrectionIdeals_of_residual
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q))) :
    ∃ N : ℕ, ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
      (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
      (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
      (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
        ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop
          t.val) → Q ^ N ≤ rankStageCoreCorrectionIdeal e n c hc J v := by
  obtain ⟨N, hN⟩ := exists_pow_le_originalBoundaryLiftIdeal_of_residual J e hJ f hf t Q hfg hQ
  exact ⟨N, fun n _ c hc v hv ↦ hN.trans
    (originalBoundaryLiftIdeal_le_correctionIdeal J t.val e n c hc v hv)⟩

variable (n : ℕ) {ι : Type} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
  (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
    ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t.val)

include hf hv in
/-- Disjoint bad-image closures kill the actual all-order correction class without scaling. -/
theorem rankStageCoreCorrection_eq_zero_of_disjoint_images
    (h : Disjoint (closure (scalarMorphism σ '' (J.support : Set A)))
      (closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ))) :
    rankStageCoreCorrectionObstruction e n c hc J v = 0 := by
  apply (one_mem_rankStageCoreCorrectionIdeal e n c hc J v).mp
  apply originalBoundaryLiftIdeal_le_correctionIdeal J t.val e n c hc v hv
  exact (one_mem_originalBoundaryLiftIdeal J t.val).mpr
    (exists_originalBoundaryLift_of_disjoint_images J e hJ f hf t h)

end FLT.Mazur.EquivalenceRelationOrderedFrames
