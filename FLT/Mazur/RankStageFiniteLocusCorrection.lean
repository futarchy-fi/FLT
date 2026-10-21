/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryScalarGeometry
public import FLT.Mazur.RankStagePrincipalBoundaryCorrection
public import FLT.Mazur.InvariantAffineFiniteBoundaryLift
public import FLT.Mazur.SchemeFiniteTargetRestriction
public import FLT.Mazur.SchemeScalarPrincipalNeighborhood

/-!
# Geometric original finite-locus control of actual rank corrections

An original invariant principal neighborhood in the finite target locus
constructs its own full boundary lift. Clearing its original denominators
gives one scalar power for every rank and core family. Consequently actual
correction support lies over the closure of the original nonfinite image,
without assuming affine full thickenings or finite clopen core covers.
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
local instance finiteCorrectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteCorrectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteCorrectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
attribute [local irreducible] rankStageCoreCorrectionIdeal

include hf in
/-- A finite original principal neighborhood constructs one correction power for all ranks. -/
theorem exists_pow_mem_rankStageCoreCorrectionIdeals_of_finite_neighborhood
    (r : compatibleFunctions p q) (hr : A.basicOpen r.val ≤ finiteTargetOpen p) :
    ∃ N : ℕ, ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
      (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
      (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
      (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
        ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop
          t.val) → r ^ N ∈ rankStageCoreCorrectionIdeal e n c hc J v := by
  let _ : IsFinite (p.resLE (A.basicOpen r.val) _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact finite_restrict_of_le_finiteTarget p _ hr
  obtain ⟨u, hu⟩ := InvariantAffineFiniteBoundaryLift.exists_lift p q e
    (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r)
    (compatibleFunctions_basicOpen_affine p q r) J hJ f hf t
  let _ := QuasiCompact.compactSpace_of_compactSpace p
  let _ := quasiSeparatedSpace_of_quasiSeparated p
  exact exists_pow_mem_all_rankStageCoreCorrectionIdeals J t.val r u hu e

variable (n : ℕ) {ι : Type} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
  (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
  (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
    ((v j).val k).val = (rankStageCoreOriginalBoundaryMap e n (c j) (hc j) J k).appTop t.val)
local notation "σ" => Subring.subtype (compatibleFunctions p q)

include hf hv in
/-- The actual all-order correction class is supported over the original nonfinite locus. -/
theorem rankStageCoreCorrection_support_subset_nonfinite_image :
    PrimeSpectrum.zeroLocus
        (rankStageCoreCorrectionIdeal e n c hc J v : Set (compatibleFunctions p q)) ⊆
      closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) := by
  intro x hx
  by_contra h
  obtain ⟨r, hrx, hr⟩ :=
    (mem_scalarNeighborhoodLocus_iff σ (finiteTargetOpen p) x).mp h
  obtain ⟨N, hN⟩ :=
    exists_pow_mem_rankStageCoreCorrectionIdeals_of_finite_neighborhood e J hJ f hf t r hr
  exact hrx (x.isPrime.mem_of_pow_mem N (hx (hN n ι c hc v hv)))

include hf hv in
/-- Both geometric bounds hold simultaneously on the unchanged original scalar spectrum. -/
theorem rankStageCoreCorrection_support_subset_boundary_nonfinite :
    PrimeSpectrum.zeroLocus
        (rankStageCoreCorrectionIdeal e n c hc J v : Set (compatibleFunctions p q)) ⊆
      closure (scalarMorphism σ '' (J.support : Set A)) ∩
        closure (scalarMorphism σ '' (finiteTargetOpen p : Set A)ᶜ) := by
  intro x hx
  exact ⟨rankStageCoreCorrection_support_subset_boundary_image J e n c hc v hx,
    rankStageCoreCorrection_support_subset_nonfinite_image e J hJ f hf t n c hc v hv hx⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
