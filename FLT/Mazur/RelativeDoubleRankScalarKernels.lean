/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankCompact
public import FLT.Mazur.RelativeRankCollisionFinite
public import FLT.Mazur.SchemeScalarAvoidanceCover
public import FLT.Mazur.SchemeScalarImageNilpotence

/-!
# Scalar equations on the full independent rank charts

Each off-diagonal chart computes its closed scalar image by the radical
of an exact full-section kernel. The geometric rank bound makes their
intersection finite. Neither reduced charts nor scalar Noetherianity is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  (x y : T ⟶ A) {R : Type} [CommRing R] (σ : R →+* Γ(T, ⊤))

/-- Exact original scalars killed on the entire independent rank thickening. -/
def doubleRankScalarKernel (n m r s : ℕ) : Ideal R :=
  RingHom.ker ((doubleRankMap E x y n m r s).appTop.hom.comp σ)

/-- The rank-pair image is computed using the full original scalar map on the stage. -/
theorem rankPair_scalarImage_eq (n m r s : ℕ) (hnm : n ≠ m) :
    scalarMorphism σ '' rankPairLocus E x y n m =
      Set.range (scalarMorphism ((doubleRankMap E x y n m r s).appTop.hom.comp σ)) := by
  have he : rankPairLocus E x y n m = Set.range (doubleRankMap E x y n m r s) := by
    rw [doubleRankMap_range]
    ext z
    exact ⟨fun hz ↦ hz.2, fun hz ↦ ⟨hnm, hz⟩⟩
  rw [he, scalarMorphism_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

variable [NoetherianSpace A] [CompactSpace T]

/-- A chart's closed scalar image has exactly the radical of its unreduced coefficient kernel. -/
theorem rankPair_vanishingIdeal_eq (n m r s : ℕ) (hnm : n ≠ m) :
    PrimeSpectrum.vanishingIdeal (scalarMorphism σ '' rankPairLocus E x y n m) =
      (doubleRankScalarKernel E x y σ n m r s).radical := by
  rw [rankPair_scalarImage_eq E x y σ n m r s hnm,
    scalarImage_vanishingIdeal_eq_kernel_radical]
  rfl

/-- Changing either order preserves the radical, while the exact kernels may change. -/
theorem doubleRankScalarKernel_radical_order_independent
    (n m r s r' s' : ℕ) (hnm : n ≠ m) :
    (doubleRankScalarKernel E x y σ n m r s).radical =
      (doubleRankScalarKernel E x y σ n m r' s').radical := by
  rw [← rankPair_vanishingIdeal_eq E x y σ n m r s hnm,
    ← rankPair_vanishingIdeal_eq E x y σ n m r' s' hnm]

/-- At any two fixed orders, exact chart kernels compute the full collision ideal. -/
theorem rankCollisionIdeal_eq_doubleRank_kernels (r s : ℕ) :
    rankCollisionIdeal E x y (scalarMorphism σ) =
      ⨅ n : ℕ, ⨅ m : ℕ, ⨅ (_ : n ≠ m),
        (doubleRankScalarKernel E x y σ n m r s).radical := by
  ext a
  simp only [Ideal.mem_iInf]
  rw [rankCollisionIdeal, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h n m hnm
    rw [← rankPair_vanishingIdeal_eq E x y σ n m r s hnm,
      PrimeSpectrum.mem_vanishingIdeal]
    rintro P ⟨z, hz, rfl⟩
    exact h _ ⟨z, ⟨n, m, hz⟩, rfl⟩
  · intro h P hP
    obtain ⟨z, ⟨n, m, hnm, hn, hm⟩, rfl⟩ := hP
    have ha := h n m hnm
    rw [← rankPair_vanishingIdeal_eq E x y σ n m r s hnm,
      PrimeSpectrum.mem_vanishingIdeal] at ha
    exact ha _ ⟨z, ⟨hnm, hn, hm⟩, rfl⟩

variable [QuasiCompact E.hom]

/-- Only finitely many full chart kernels contribute, with no scalar finiteness assumption. -/
theorem exists_rankCollisionIdeal_finite_kernels (r s : ℕ) :
    ∃ N : ℕ, rankCollisionIdeal E x y (scalarMorphism σ) =
      ⨅ n : Fin (N + 1), ⨅ m : Fin (N + 1), ⨅ (_ : n.val ≠ m.val),
        (doubleRankScalarKernel E x y σ n.val m.val r s).radical := by
  obtain ⟨N, hN⟩ := exists_rankCollisionIdeal_finite E x y (scalarMorphism σ)
  refine ⟨N, hN.trans ?_⟩
  congr 1
  funext n
  congr 1
  funext m
  by_cases hnm : n.val = m.val
  · simp only [rankPairLocus, hnm, ne_eq, not_true_eq_false, false_and,
      Set.ofPred_false, Set.image_empty, PrimeSpectrum.vanishingIdeal_empty, iInf_of_empty]
  · simp only [iInf_pos hnm]
    exact rankPair_vanishingIdeal_eq E x y σ n.val m.val r s hnm

end FLT.Mazur.RelativeOrderedTuples
