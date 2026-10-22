/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankExactDenominators
public import FLT.Mazur.SchemeFiniteCoverScalarKernel

/-!
# Complete finite independent rank kernels

Including equal-rank charts gives a family covering the whole coefficient
scheme. One rank rectangle works at every pair of orders. Its exact kernel
recovers the original scalar kernel up to radical, without reducing any chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  (x y : T ⟶ A) {R : Type} [CommRing R] (σ : R →+* Γ(T, ⊤))

/-- Exact equations on all charts, including the diagonal, of a finite rank rectangle. -/
def doubleRankCompleteKernel (N r s : ℕ) : Ideal R :=
  ⨅ i : Fin (N + 1) × Fin (N + 1),
    doubleRankScalarKernel E x y σ i.1.val i.2.val r s

/-- Complete kernel membership retains each full coefficient equation. -/
theorem mem_doubleRankCompleteKernel (N r s : ℕ) (a : R) :
    a ∈ doubleRankCompleteKernel E x y σ N r s ↔
      ∀ n m : Fin (N + 1),
        (doubleRankMap E x y n.val m.val r s).appTop (σ a) = 0 := by
  simp only [doubleRankCompleteKernel, Ideal.mem_iInf, Prod.forall]
  rfl

/-- Every original scalar equation remains an equation on the entire rectangle. -/
theorem scalarKernel_le_doubleRankCompleteKernel (N r s : ℕ) :
    RingHom.ker σ ≤ doubleRankCompleteKernel E x y σ N r s := by
  intro a ha
  apply (mem_doubleRankCompleteKernel E x y σ N r s a).mpr
  intro n m
  rw [show σ a = 0 from ha, map_zero]

/-- Removing the equal-rank tests loses equations, so only this containment is automatic. -/
theorem doubleRankCompleteKernel_le_collision (N r s : ℕ) :
    doubleRankCompleteKernel E x y σ N r s ≤
      doubleRankCollisionKernel E x y σ N r s := by
  intro a ha
  exact (mem_doubleRankCollisionKernel E x y σ N r s a).mpr
    (fun n m _ ↦ (mem_doubleRankCompleteKernel E x y σ N r s a).mp ha n m)

variable [NoetherianSpace A] [CompactSpace T] [QuasiCompact E.hom]

/-- One complete finite rectangle detects original scalar nilpotence at all two orders. -/
theorem exists_uniform_doubleRank_complete_kernel :
    ∃ N : ℕ, ∀ r s : ℕ,
      (doubleRankCompleteKernel E x y σ N r s).radical =
        (RingHom.ker σ).radical := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  refine ⟨N, fun r s ↦ ?_⟩
  apply finite_cover_scalar_kernel_radical
    (fun i : Fin (N + 1) × Fin (N + 1) ↦
      doubleRankMap E x y i.1.val i.2.val r s) σ
  intro z
  obtain ⟨n, m, w, hw⟩ := exists_doubleRank_lift E x y r s z
  obtain ⟨hx, hy⟩ := doubleRankMap_endpoints E x y n m r s w
  exact ⟨(⟨n, Nat.lt_succ_of_le (hN _ n hx.1)⟩,
    ⟨m, Nat.lt_succ_of_le (hN _ m hy.1)⟩), w, hw⟩

end FLT.Mazur.RelativeOrderedTuples
