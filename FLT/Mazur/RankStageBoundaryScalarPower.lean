/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryScalarGeometry
public import FLT.Mazur.RankStageOriginalScalarSupport
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# One original ideal power for all full boundary correction classes

A geometric test on the entire original boundary yields one power of the
original scalar ideal. Noetherianity is used only on the original affine
source coordinates. The exponent works for every rank, core family and
cochain; no finiteness of the invariant ring or full correction cokernel
is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [IsLocallyNoetherian A]
  (J : A.IdealSheafData) (Q : Ideal (compatibleFunctions p q))
local notation "σ" => Subring.subtype (compatibleFunctions p q)

/-- A whole-boundary geometric test gives one exact original ideal power in the full kernel. -/
theorem exists_pow_le_originalBoundaryScalarKernel
    (hQ : ∀ x : A, x ∈ J.support →
      scalarMorphism σ x ∈ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q))) :
    ∃ N : ℕ, Q ^ N ≤ originalBoundaryScalarKernel (p := p) (q := q) J := by
  let I := J.ideal ⟨⊤, isAffineOpen_top A⟩
  have hz : PrimeSpectrum.zeroLocus (I : Set Γ(A, ⊤)) ⊆
      PrimeSpectrum.zeroLocus (Q.map σ : Set Γ(A, ⊤)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := A.toSpecΓ.homeomorph.surjective y
    apply (A.toSpecΓ_preimage_zeroLocus (Q.map σ : Set Γ(A, ⊤))).ge
    apply (SchemeScalarPulledIdealSupport.mem_scalar_zeroLocus_iff σ Q x).mp
    apply hQ x
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := J) (U := ⟨⊤, isAffineOpen_top A⟩) (x := x) trivial).mpr
    exact (A.toSpecΓ_preimage_zeroLocus (I : Set Γ(A, ⊤))).le hy
  have hr : Q.map σ ≤ I.radical := (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hz
  let _ := IsLocallyNoetherian.component_noetherian
    (⟨⊤, isAffineOpen_top A⟩ : A.affineOpens)
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr
    (IsNoetherian.noetherian (Q.map σ))
  refine ⟨N, ?_⟩
  rw [originalBoundaryScalarKernel_eq_comap, ← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact hN

variable [IsSeparated p] [Etale p] [QuasiCompact p] [Etale q] [LocallyQuasiFinite p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryPowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryPowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryPowerOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local irreducible] rankStageCoreCorrectionIdeal

/-- One original ideal power corrects all cochains on every rank and every whole core family. -/
theorem exists_pow_le_all_rankStageCoreCorrectionIdeals
    (hQ : ∀ x : A, x ∈ J.support →
      scalarMorphism σ x ∈ PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q))) :
    ∃ N : ℕ, ∀ (n : ℕ) (ι : Type) (c : ι → Γ(A, ⊤))
      (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n)
      (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
      Q ^ N ≤ rankStageCoreCorrectionIdeal e n c hc J v := by
  obtain ⟨N, hN⟩ := exists_pow_le_originalBoundaryScalarKernel J Q hQ
  exact ⟨N, fun n _ c hc v ↦ hN.trans
    (originalBoundaryScalarKernel_le_correctionIdeal e n c hc J v)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
