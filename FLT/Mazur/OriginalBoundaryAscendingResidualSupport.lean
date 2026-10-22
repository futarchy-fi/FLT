/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAscendingRankKernel
public import FLT.Mazur.OriginalBoundaryUniformResidualRankEquations

/-!
# Ascending chart criteria for the unchanged residual rank support

Transposition and order-independent support reduce the geometric obligations
to strictly ascending ranks at one prescribed pair of orders. The residual
ideal keeps both bad closures. The remaining chart containments are still
required; no correction or comparison coverage is inferred without them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem radical_sup_eq_of_radical_eq {R : Type} [CommRing R]
    {I K : Ideal R} (H : Ideal R) (h : I.radical = K.radical) :
    (I ⊔ H).radical = (K ⊔ H).radical := by
  calc
    (I ⊔ H).radical = (I.radical ⊔ H.radical).radical := Ideal.radical_sup I H
    _ = (K.radical ⊔ H.radical).radical := congrArg (fun L ↦ (L ⊔ H.radical).radical) h
    _ = (K ⊔ H).radical := (Ideal.radical_sup K H).symm

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance ascendingResidualOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance ascendingResidualOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J
variable [IsAffine A] [TopologicalSpace.NoetherianSpace A]
local instance ascendingResidualBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι

/-- The unchanged residual sum has order-independent radical on each unequal-rank chart. -/
theorem originalBoundary_doubleRank_residual_radical_order
    (n m r s r' s' : ℕ) (hnm : n ≠ m) :
    (doubleRankScalarKernel (Over.mk p) x y σ n m r s ⊔ H).radical =
      (doubleRankScalarKernel (Over.mk p) x y σ n m r' s' ⊔ H).radical := by
  exact radical_sup_eq_of_radical_eq H
    (doubleRankScalarKernel_radical_order_independent (Over.mk p) x y σ n m r s r' s' hnm)

/-- At the level of support, transposition also permits keeping the prescribed orders fixed. -/
theorem originalBoundary_doubleRank_residual_radical_swap
    (n m r s : ℕ) (hnm : n ≠ m) :
    (doubleRankScalarKernel (Over.mk p) x y σ n m r s ⊔ H).radical =
      (doubleRankScalarKernel (Over.mk p) x y σ m n r s ⊔ H).radical := by
  exact (congrArg Ideal.radical
    (originalBoundary_doubleRank_residual_transpose J n m r s)).trans
      (originalBoundary_doubleRank_residual_radical_order J m n s r r s hnm.symm)

/-- All off-diagonal geometric containments are equivalent to the ascending ones. -/
theorem originalBoundary_residual_charts_iff_ascending (N r s : ℕ) (Q : Ideal R) :
    (∀ n m : Fin (N + 1), n.val ≠ m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical) ↔
      ∀ n m : Fin (N + 1), n.val < m.val →
        Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical := by
  constructor
  · exact fun h n m hnm ↦ h n m (Nat.ne_of_lt hnm)
  · intro h n m hnm
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · exact h n m hlt
    · exact (h m n hgt).trans
        (originalBoundary_doubleRank_residual_radical_swap J m.val n.val r s hnm.symm).le

/-- Ascending corrections at one pair of orders control all off-diagonal radical obligations. -/
theorem originalBoundary_ascending_residual_all_orders
    (N r s : ℕ) (Q : Ideal R)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical)
    (r' s' : ℕ) :
    ∀ n m : Fin (N + 1), n.val ≠ m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r' s' ⊔ H).radical := by
  intro n m hnm
  exact ((originalBoundary_residual_charts_iff_ascending J N r s Q).mpr h n m hnm).trans
    (originalBoundary_doubleRank_residual_radical_order J n.val m.val r s r' s' hnm).le

variable [QuasiCompact p]

/-- One finite ascending family tests the entire original residual support against the whole Q. -/
theorem exists_originalBoundary_ascending_residual_support_criterion :
    ∃ N : ℕ, ∀ (r s : ℕ) (Q : Ideal R) (_ : Q.FG),
      (PrimeSpectrum.zeroLocus
          (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) ↔
      ∀ n m : Fin (N + 1), n.val < m.val →
        Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_uniform_residual_chart_criterion (p := p) (q := q) J
  exact ⟨N, fun r s Q hfg ↦ (hN r s Q hfg).trans
    (originalBoundary_residual_charts_iff_ascending J N r s Q)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
