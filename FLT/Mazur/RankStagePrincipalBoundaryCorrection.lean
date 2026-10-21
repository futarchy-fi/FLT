/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageOriginalBoundaryLiftIdeal
public import FLT.Mazur.SchemeRelationQcqsIdealBoundaryNumerator

/-!
# Actual rank corrections from original principal boundary lifts

A full boundary lift on one original invariant principal neighborhood gives
a power of the very same original scalar in the correction ideal. Denominator
clearing takes place on the original source and its entire relation, before
restriction to rank orders. The exponent is independent of the rank and cores.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [CompactSpace D] [QuasiSeparatedSpace D]
  (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤)) (r : compatibleFunctions p q)
variable (u : InvariantOpenCoefficientRestriction.coefficients p q
  (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r))
  (hu : (J.comap (A.basicOpen r.val).ι).subschemeι.appTop u.val =
    (IdealSheafClosedTransitions.map (J.comap (A.basicOpen r.val).ι) J
      (A.basicOpen r.val).ι rfl).appTop t)

include hu in
/-- Local full boundary solvability gives an exact original-source lift after one scalar power. -/
theorem exists_pow_mem_originalBoundaryLiftIdeal :
    ∃ N : ℕ, r ^ N ∈ originalBoundaryLiftIdeal (p := p) (q := q) J t := by
  let _ : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  obtain ⟨N, w, hw, _⟩ :=
    SchemeRelationQcqsBoundaryNumerator.exists_ideal_boundary_numerator
      p q r J (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r) rfl u t hu
  refine ⟨N, w, ?_⟩
  change J.subschemeι.appTop w.val = J.subschemeι.appTop (r.val ^ N) * t
  rw [map_pow]
  exact hw

variable [IsSeparated p] [Etale p] [QuasiCompact p] [Etale q]
  [IsLocallyNoetherian A] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance principalCorrectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance principalCorrectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance principalCorrectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCoreCorrectionIdeal

include hu in
/-- One unchanged original scalar power works for every rank and every admissible core lift. -/
theorem exists_pow_mem_all_rankStageCoreCorrectionIdeals :
    ∃ N : ℕ, ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
      (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
      (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
      (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
        ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t) →
      r ^ N ∈ rankStageCoreCorrectionIdeal e n c hc J v := by
  obtain ⟨N, hN⟩ := exists_pow_mem_originalBoundaryLiftIdeal J t r u hu
  exact ⟨N, fun n _ c hc v hv ↦
    originalBoundaryLiftIdeal_le_correctionIdeal J t e n c hc v hv hN⟩

include hu in
/-- An original prime in the principal neighborhood is off the actual correction support. -/
theorem rankStageCoreCorrection_avoids_of_principal_lift
    (x : PrimeSpectrum (compatibleFunctions p q)) (hx : r ∉ x.asIdeal)
    (n : ℕ) {ι : Type} (c : ι → Γ(A, ⊤))
    (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
    (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
    (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
      ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t) :
    x ∉ PrimeSpectrum.zeroLocus
      (rankStageCoreCorrectionIdeal e n c hc J v : Set (compatibleFunctions p q)) := by
  obtain ⟨N, hN⟩ := exists_pow_mem_all_rankStageCoreCorrectionIdeals J t r u hu e
  intro h
  exact hx (x.isPrime.mem_of_pow_mem N (h (hN n ι c hc v hv)))

end FLT.Mazur.EquivalenceRelationOrderedFrames
