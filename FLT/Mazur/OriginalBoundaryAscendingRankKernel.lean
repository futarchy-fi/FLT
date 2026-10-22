/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankTransposition

/-!
# Ascending original rank equations

The full off-diagonal kernel is the intersection of two ascending-rank kernels,
one for each ordering of the infinitesimal orders. At equal orders only one
ascending family remains. These are exact full-section identities.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem ordered_kernel_inf {R : Type} [CommRing R]
    (K : ℕ → ℕ → ℕ → ℕ → Ideal R)
    (hK : ∀ n m r s, K n m r s = K m n s r) (N r s : ℕ) :
    (⨅ n : Fin (N + 1), ⨅ m : Fin (N + 1), ⨅ (_ : n.val ≠ m.val),
      K n.val m.val r s) =
    (⨅ i : {i : Fin (N + 1) × Fin (N + 1) // i.1.val < i.2.val},
      K i.val.1.val i.val.2.val r s) ⊓
    (⨅ i : {i : Fin (N + 1) × Fin (N + 1) // i.1.val < i.2.val},
      K i.val.1.val i.val.2.val s r) := by
  ext a
  simp only [Ideal.mem_inf, Ideal.mem_iInf]
  constructor
  · intro h
    refine ⟨fun i ↦ h i.val.1 i.val.2 (Nat.ne_of_lt i.property), fun i ↦ ?_⟩
    exact (hK i.val.2.val i.val.1.val r s).le
      (h i.val.2 i.val.1 (Nat.ne_of_gt i.property))
  · rintro ⟨h, h'⟩ n m hnm
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · exact h ⟨(n, m), hlt⟩
    · exact (hK m.val n.val s r).le (h' ⟨(m, n), hgt⟩)

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance ascendingOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance ascendingOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))

/-- Strictly ascending ranks index one chart from each transposition pair. -/
abbrev originalBoundaryAscendingRanks (N : ℕ) :=
  {i : Fin (N + 1) × Fin (N + 1) // i.1.val < i.2.val}

/-- Exact original scalar equations on all ascending charts at the prescribed two orders. -/
def originalBoundaryAscendingRankKernel (N r s : ℕ) : Ideal R :=
  ⨅ i : originalBoundaryAscendingRanks N,
    doubleRankScalarKernel (Over.mk p) x y σ i.val.1.val i.val.2.val r s

/-- Ascending membership retains the complete coefficient equation on every indexed chart. -/
theorem mem_originalBoundaryAscendingRankKernel (N r s : ℕ) (a : R) :
    a ∈ originalBoundaryAscendingRankKernel (p := p) (q := q) J N r s ↔
      ∀ n m : Fin (N + 1), n.val < m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) = 0 := by
  simp only [originalBoundaryAscendingRankKernel, Ideal.mem_iInf]
  exact ⟨fun h n m hnm ↦ h ⟨(n, m), hnm⟩, fun h i ↦ h i.val.1 i.val.2 i.property⟩

/-- Both order orientations of the ascending family recover every exact off-diagonal equation. -/
theorem originalBoundaryDoubleRankKernel_eq_ascending (N r s : ℕ) :
    originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s =
      originalBoundaryAscendingRankKernel (p := p) (q := q) J N r s ⊓
        originalBoundaryAscendingRankKernel (p := p) (q := q) J N s r := by
  exact ordered_kernel_inf
    (fun n m r s ↦ doubleRankScalarKernel (Over.mk p) x y σ n m r s)
    (originalBoundary_doubleRank_kernel_transpose J) N r s

/-- At equal orders the exact collision equations need only strictly ascending ranks. -/
theorem originalBoundaryDoubleRankKernel_eq_ascending_same_order (N r : ℕ) :
    originalBoundaryDoubleRankKernel (p := p) (q := q) J N r r =
      originalBoundaryAscendingRankKernel (p := p) (q := q) J N r r := by
  rw [originalBoundaryDoubleRankKernel_eq_ascending, inf_idem]

/-- Exchanging the orders leaves the exact original collision kernel unchanged. -/
theorem originalBoundaryDoubleRankKernel_order_swap (N r s : ℕ) :
    originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s =
      originalBoundaryDoubleRankKernel (p := p) (q := q) J N s r := by
  rw [originalBoundaryDoubleRankKernel_eq_ascending,
    originalBoundaryDoubleRankKernel_eq_ascending, inf_comm]

end FLT.Mazur.EquivalenceRelationOrderedFrames
