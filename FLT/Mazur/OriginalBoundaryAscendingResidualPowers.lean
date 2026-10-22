/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAscendingResidualSupport

/-!
# Shared full corrections from ascending rank charts

At equal orders a product over only the ascending charts constructs one shared
original residual correction, with an explicit exponent. Ascending radical
containments at one pair of orders give full off-diagonal ideal-power corrections
at every independent pair of orders. No powers or nilpotents are cancelled.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance ascendingPowerOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance ascendingPowerOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

/-- Only ascending charts contribute to the explicit equal-order correction exponent. -/
theorem originalBoundary_ascending_residual_power_le (N r : ℕ) (Q : Ideal R) (k : ℕ)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ^ k ≤ doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r r ⊔ H) :
    Q ^ (Nat.card (originalBoundaryAscendingRanks N) * k) ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r r := by
  have hp : Q ^ (Nat.card (originalBoundaryAscendingRanks N) * k) ≤
      originalBoundaryAscendingRankKernel (p := p) (q := q) J N r r ⊔ H :=
    FiniteScalarResidualCorrections.pow_le_shared_kernel
      (fun i : originalBoundaryAscendingRanks N ↦
        (doubleRankMap (Over.mk p) x y i.val.1.val i.val.2.val r r).appTop.hom.comp σ)
      H Q k (fun i ↦ h i.val.1 i.val.2 i.property)
  exact hp.trans (sup_le_sup_right
    (originalBoundaryDoubleRankKernel_eq_ascending_same_order J N r).symm.le H)

/-- The product constructs one original residual scalar solving every full off-diagonal row. -/
theorem originalBoundary_ascending_shared_correction (N r : ℕ) (Q : Ideal R) (k : ℕ)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ^ k ≤ doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r r ⊔ H)
    (a : R) (ha : a ∈ Q ^ (Nat.card (originalBoundaryAscendingRanks N) * k)) :
    ∃ b ∈ H, ∀ n m : Fin (N + 1), n.val ≠ m.val →
      (doubleRankMap (Over.mk p) x y n.val m.val r r).appTop (σ a) =
        (doubleRankMap (Over.mk p) x y n.val m.val r r).appTop (σ b) :=
  (mem_originalBoundaryResidualDoubleRankIdeal J N r r a).mp
    (originalBoundary_ascending_residual_power_le J N r Q k h ha)

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A]

/-- One ascending support calculation supplies exact ideal powers at every independent order. -/
theorem originalBoundary_ascending_residual_powers_all_orders
    (N r s : ℕ) (Q : Ideal R) (hfg : Q.FG)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical)
    (r' s' : ℕ) :
    ∃ k : ℕ, Q ^ k ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r' s' :=
  exists_originalBoundary_doubleRank_residual_power J N r' s' Q hfg
    (originalBoundary_ascending_residual_all_orders J N r s Q h r' s')

end FLT.Mazur.EquivalenceRelationOrderedFrames
