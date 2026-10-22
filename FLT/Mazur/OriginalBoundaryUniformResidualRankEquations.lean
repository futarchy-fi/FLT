/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankResidualCorrections
public import FLT.Mazur.RelativeDoubleRankUniformRectangle

/-!
# One original residual rank rectangle for all infinitesimal orders

A single geometric rectangle works for every pair of orders. Its separate
chart equations, with the unchanged original residual ideal, suffice to prove
the whole support bound. Chartwise containments remain geometric obligations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem radical_le_finite_kernel_iff {R : Type} [CommRing R]
    {ι : Type} [Finite ι] {B : ι → Type} [∀ i, CommRing (B i)]
    (φ : ∀ i, R →+* B i) (H Q : Ideal R) (hfg : Q.FG) :
    Q ≤ ((⨅ i, RingHom.ker (φ i)) ⊔ H).radical ↔
      ∀ i, Q ≤ (RingHom.ker (φ i) ⊔ H).radical := by
  constructor
  · intro h i
    exact h.trans (Ideal.radical_mono (sup_le_sup_right (iInf_le _ i) H))
  · intro h
    obtain ⟨k, hk⟩ := FiniteScalarResidualCorrections.exists_pow_le_shared_kernel φ H Q hfg h
    intro a ha
    exact ⟨k, hk (Ideal.pow_mem_pow ha k)⟩

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
local instance uniformResidualOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance uniformResidualOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance uniformResidualOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
  doubleRankCollisionKernel originalBoundaryResidualRankIdeal
  originalBoundaryResidualDoubleRankIdeal
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J
variable [IsAffine A] [TopologicalSpace.NoetherianSpace A]
local instance uniformResidualBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι

/-- One finite original rectangle computes the unchanged residual support at all two orders. -/
theorem exists_originalBoundary_uniform_residual_equations :
    ∃ N : ℕ, ∀ r s : ℕ,
      PrimeSpectrum.zeroLocus
          (originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s : Set R) =
        PrimeSpectrum.zeroLocus
          (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) := by
  obtain ⟨N, hN⟩ := exists_uniform_doubleRank_collision_rectangle (Over.mk p) x y σ
  refine ⟨N, fun r s ↦ ?_⟩
  have hkernel : originalBoundaryRankCollisionIdeal (p := p) (q := q) J =
      (originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s).radical := by
    simpa only [originalBoundaryRankCollisionIdeal, originalBoundaryDoubleRankKernel,
      scalarMorphism_comp] using hN r s
  rw [originalBoundaryResidualDoubleRankIdeal, originalBoundaryResidualRankIdeal,
    PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_sup, hkernel,
    PrimeSpectrum.zeroLocus_radical]

/-- The full residual support bound can be proved separately on each full coefficient chart. -/
theorem exists_originalBoundary_uniform_residual_chart_criterion :
    ∃ N : ℕ, ∀ (r s : ℕ) (Q : Ideal R) (_ : Q.FG),
      (PrimeSpectrum.zeroLocus
          (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) ↔
      ∀ n m : Fin (N + 1), n.val ≠ m.val →
        Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_uniform_residual_equations (p := p) (q := q) J
  refine ⟨N, fun r s Q hfg ↦ ?_⟩
  simp only [← hN r s, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff,
    originalBoundaryResidualDoubleRankIdeal, originalBoundaryDoubleRankKernel,
    doubleRankCollisionKernel_eq_offDiagonal, radical_le_finite_kernel_iff _ _ Q hfg]
  exact ⟨fun h n m hnm ↦ h ⟨(n, m), hnm⟩,
    fun h i ↦ h i.val.1 i.val.2 i.property⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
