/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankScalarKernel
public import FLT.Mazur.OriginalBoundaryResidualRankObstruction

/-!
# Exact independent-rank equations for the full residual support bound

At any prescribed pair of orders the residual rank obstruction is cut out
by an exact finite chart-kernel intersection plus the unchanged residual
ideal. The latter retains both original bad closures. For an explicitly
finitely generated Q, the whole V(Q) support bound is equivalent to a power
containment in this exact sum. The containment still needs to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem support_iff_pow_le {R : Type} [CommRing R]
    (I Q : Ideal R) (hfg : Q.FG) :
    (PrimeSpectrum.zeroLocus (I : Set R) ⊆ PrimeSpectrum.zeroLocus (Q : Set R)) ↔
      ∃ k : ℕ, Q ^ k ≤ I := by
  rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  refine ⟨fun h ↦ Ideal.exists_pow_le_of_le_radical_of_fg h hfg, ?_⟩
  rintro ⟨k, hk⟩ a ha
  exact ⟨k, hk (Ideal.pow_mem_pow ha k)⟩

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
local notation "R" => invariants p.appTop.hom q.appTop.hom

/-- Exact full chart equations together with the original two-closure residual ideal. -/
def originalBoundaryResidualDoubleRankIdeal (N r s : ℕ) : Ideal R :=
  originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s ⊔
    originalBoundaryResidualIdeal (p := p) (q := q) J

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A]

/-- The constructed full coefficient ideal has exactly the entire original residual support. -/
theorem exists_originalBoundary_residual_exact_equations (r s : ℕ) :
    ∃ N : ℕ,
      PrimeSpectrum.zeroLocus
          (originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s : Set R) =
        PrimeSpectrum.zeroLocus
          (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_rank_kernel_radical (p := p) (q := q) J r s
  refine ⟨N, ?_⟩
  rw [originalBoundaryResidualDoubleRankIdeal, originalBoundaryResidualRankIdeal,
    PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_sup, hN,
    PrimeSpectrum.zeroLocus_radical]

/-- One finite rank rectangle works for every finitely generated original target ideal. -/
theorem originalBoundary_residual_support_iff_exact_power (r s : ℕ) :
    ∃ N : ℕ, ∀ (Q : Ideal R) (_ : Q.FG),
      (PrimeSpectrum.zeroLocus
          (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) ↔
      ∃ k : ℕ, Q ^ k ≤
        originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_residual_exact_equations (p := p) (q := q) J r s
  refine ⟨N, fun Q hfg ↦ ?_⟩
  rw [← hN]
  exact support_iff_pow_le _ Q hfg

/-- A proved full support bound yields exact equations at every prescribed pair of orders. -/
theorem originalBoundary_residual_exact_power (Q : Ideal R) (hfg : Q.FG)
    (hQ : PrimeSpectrum.zeroLocus
      (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) (r s : ℕ) :
    ∃ N k : ℕ, Q ^ k ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s := by
  obtain ⟨N, hN⟩ := originalBoundary_residual_support_iff_exact_power (p := p) (q := q) J r s
  obtain ⟨k, hk⟩ := (hN Q hfg).mp hQ
  exact ⟨N, k, hk⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
