/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPositiveRankStages
public import FLT.Mazur.OriginalBoundaryAscendingResidualPowers

/-!
# Residual corrections indexed only by positive ascending ranks

Reflexivity discharges every zero-rank chart geometrically. The unchanged
ascending scalar kernel is therefore the intersection over positive ranks.
The finite correction product needs only these factors. Both original bad
closures and the whole target ideal remain in every support statement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData) (e : CategoryTheory.EquivalenceRelation p q)
local instance positiveResidualOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance positiveResidualOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

/-- Only strictly positive ascending ranks contribute nonempty original charts. -/
abbrev originalBoundaryPositiveAscendingRanks (N : ℕ) :=
  {i : Fin (N + 1) × Fin (N + 1) // 0 < i.1.val ∧ i.1.val < i.2.val}

include e in
/-- Discarding zero-rank factors is an exact kernel identity, without taking radicals. -/
theorem originalBoundary_ascendingKernel_eq_positive (N r s : ℕ) :
    originalBoundaryAscendingRankKernel (p := p) (q := q) J N r s =
      ⨅ i : originalBoundaryPositiveAscendingRanks N,
        doubleRankScalarKernel (Over.mk p) x y σ i.val.1.val i.val.2.val r s := by
  ext a
  simp only [originalBoundaryAscendingRankKernel, Ideal.mem_iInf]
  constructor
  · exact fun h i ↦ h ⟨i.val, i.property.2⟩
  · intro h i
    by_cases hn : i.val.1.val = 0
    · rw [original_doubleRank_zero_kernel_top e x y i.val.1.val i.val.2.val r s σ
        (Or.inl hn)]
      trivial
    · exact h ⟨i.val, Nat.pos_of_ne_zero hn, i.property⟩

include e in
/-- The correction exponent counts only the genuinely possible positive ascending charts. -/
theorem originalBoundary_positive_residual_power_le (N r : ℕ) (Q : Ideal R) (d : ℕ)
    (h : ∀ n m : Fin (N + 1), 0 < n.val → n.val < m.val →
      Q ^ d ≤ doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r r ⊔ H) :
    Q ^ (Nat.card (originalBoundaryPositiveAscendingRanks N) * d) ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r r := by
  have hp := FiniteScalarResidualCorrections.pow_le_shared_kernel
    (fun i : originalBoundaryPositiveAscendingRanks N ↦
      (doubleRankMap (Over.mk p) x y i.val.1.val i.val.2.val r r).appTop.hom.comp σ)
    H Q d (fun i ↦ h i.val.1 i.val.2 i.property.1 i.property.2)
  have he := (originalBoundaryDoubleRankKernel_eq_ascending_same_order J N r).trans
    (originalBoundary_ascendingKernel_eq_positive J e N r r)
  exact hp.trans (sup_le_sup_right he.symm.le H)

include e in
/-- Positive ascending containments discharge all ascending support obligations. -/
theorem originalBoundary_ascending_radical_iff_positive (N r s : ℕ) (Q : Ideal R) :
    (∀ n m : Fin (N + 1), n.val < m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical) ↔
    ∀ n m : Fin (N + 1), 0 < n.val → n.val < m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical := by
  constructor
  · exact fun h n m _ hnm ↦ h n m hnm
  · intro h n m hnm
    by_cases hn : n.val = 0
    · rw [original_doubleRank_zero_kernel_top e x y n.val m.val r s σ (Or.inl hn),
        top_sup_eq, Ideal.radical_top]
      exact le_top
    · exact h n m (Nat.pos_of_ne_zero hn) hnm

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A] [QuasiCompact p]

include e in
/-- The entire residual support is tested on positive ascending ranks at any one order pair. -/
theorem exists_originalBoundary_positive_residual_support_criterion :
    ∃ N : ℕ, ∀ (r s : ℕ) (Q : Ideal R) (_ : Q.FG),
      (PrimeSpectrum.zeroLocus
          (originalBoundaryResidualRankIdeal (p := p) (q := q) J : Set R) ⊆
        PrimeSpectrum.zeroLocus (Q : Set R)) ↔
      ∀ n m : Fin (N + 1), 0 < n.val → n.val < m.val →
        Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_ascending_residual_support_criterion
    (p := p) (q := q) J
  exact ⟨N, fun r s Q hfg ↦ (hN r s Q hfg).trans
    (originalBoundary_ascending_radical_iff_positive J e N r s Q)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
