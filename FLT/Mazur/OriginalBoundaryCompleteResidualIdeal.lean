/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryCompleteRankKernel

/-!
# Residual corrections on the complete rank rectangle

The sum of the complete chart kernel and the unchanged residual ideal has
exactly the original residual support. Both bad closures and every equal-rank
chart are retained. A shared scalar correction is still an exact full-section
equation; only the comparison of supports takes radicals.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance completeResidualOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance completeResidualOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

/-- Complete exact rank equations plus the original residual ideal. -/
def originalBoundaryCompleteResidualIdeal (N r s : ℕ) : Ideal R :=
  originalBoundaryCompleteRankKernel (p := p) (q := q) J N r s ⊔ H

/-- One original residual scalar corrects every chart, including all equal-rank charts. -/
theorem mem_originalBoundaryCompleteResidualIdeal (N r s : ℕ) (a : R) :
    a ∈ originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s ↔
      ∃ b ∈ H, ∀ n m : Fin (N + 1),
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) =
          (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ b) := by
  have h := FiniteScalarResidualCorrections.mem_iInf_kernel_sup_iff
    (fun i : Fin (N + 1) × Fin (N + 1) ↦
      (doubleRankMap (Over.mk p) x y i.1.val i.2.val r s).appTop.hom.comp σ) H a
  change (a ∈ originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s) ↔
    ∃ b ∈ H, ∀ i : Fin (N + 1) × Fin (N + 1),
      (doubleRankMap (Over.mk p) x y i.1.val i.2.val r s).appTop (σ a) =
        (doubleRankMap (Over.mk p) x y i.1.val i.2.val r s).appTop (σ b) at h
  simpa only [Prod.forall] using h

/-- The complete correction ideal is contained in the off-diagonal correction ideal. -/
theorem originalBoundaryCompleteResidualIdeal_le_offDiagonal (N r s : ℕ) :
    originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s :=
  sup_le_sup_right (doubleRankCompleteKernel_le_collision (Over.mk p) x y σ N r s) H

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A] [QuasiCompact p]

/-- A fixed complete rectangle retains exactly the whole original residual support. -/
theorem exists_originalBoundary_complete_residual_radical :
    ∃ N : ℕ, ∀ r s : ℕ,
      (originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s).radical =
        (H).radical := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_complete_rank_kernel (p := p) (q := q) J
  refine ⟨N, fun r s ↦ ?_⟩
  change (_ ⊔ H).radical = (H).radical
  rw [Ideal.radical_sup, hN r s]
  have hle : (originalBoundaryScalarKernel (p := p) (q := q) J).radical ≤ (H).radical :=
    Ideal.radical_mono le_sup_left
  rw [sup_eq_right.mpr hle, Ideal.radical_idem]

/-- Every two-order complete family cuts out both original bad closures, with no extra locus. -/
theorem exists_originalBoundary_complete_residual_support :
    ∃ N : ℕ, ∀ r s : ℕ,
      PrimeSpectrum.zeroLocus
          (originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s : Set R) =
        PrimeSpectrum.zeroLocus
          (originalBoundaryResidualIdeal (p := p) (q := q) J :
            Set (SchemeEffectiveEpiSections.compatibleFunctions p q)) := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_complete_residual_radical (p := p) (q := q) J
  refine ⟨N, fun r s ↦ ?_⟩
  rw [← PrimeSpectrum.zeroLocus_radical, hN r s, PrimeSpectrum.zeroLocus_radical]

end FLT.Mazur.EquivalenceRelationOrderedFrames
