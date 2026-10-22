/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAscendingResidualPowers
public import FLT.Mazur.RelativeDoubleRankCofinalEquations

/-!
# One original residual correction across bounded independent orders

The original residual ideal retains both bad closures. A correction at a
common upper order restricts to one and the same scalar at every smaller pair.
Ascending geometric containments therefore give a uniform power on any bounded
order rectangle, without assuming a uniform power at all unbounded orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance boundedOrderOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundedOrderOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

/-- Full original residual equations restrict along both order increases. -/
theorem originalBoundary_residual_orders_antitone (N : ℕ) {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r' s' ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s :=
  sup_le_sup_right (doubleRankCollisionKernel_antitone (Over.mk p) x y σ N hr hs) H

/-- One residual scalar corrects all full rank charts throughout the bounded order rectangle. -/
theorem originalBoundary_bounded_order_shared_correction (N k : ℕ) (a : R)
    (ha : a ∈ originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N k k) :
    ∃ b ∈ H, ∀ r s : ℕ, r ≤ k → s ≤ k →
      ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) =
          (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ b) := by
  let hc := (mem_originalBoundaryResidualDoubleRankIdeal J N k k a).mp ha
  let b := hc.choose
  have hb := hc.choose_spec.1
  have hab := hc.choose_spec.2
  exact ⟨b, hb, fun r s hr hs n m hnm ↦
    doubleRankTransition_section_eq (Over.mk p) x y n.val m.val hr hs
      (σ a) (σ b) (hab n m hnm)⟩

/-- An explicit ascending-chart power works at every smaller independent pair of orders. -/
theorem originalBoundary_ascending_bounded_order_power (N k : ℕ) (Q : Ideal R) (d : ℕ)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ^ d ≤ doubleRankScalarKernel (Over.mk p) x y σ n.val m.val k k ⊔ H)
    (r s : ℕ) (hr : r ≤ k) (hs : s ≤ k) :
    Q ^ (Nat.card (originalBoundaryAscendingRanks N) * d) ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s :=
  (originalBoundary_ascending_residual_power_le J N k Q d h).trans
    (originalBoundary_residual_orders_antitone J N hr hs)

/-- All exact residual orders are cofinally tested by ascending ranks at equal orders. -/
theorem originalBoundary_residual_iInf_ascending_equal_orders (N : ℕ) :
    (⨅ r : ℕ, ⨅ s : ℕ,
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s) =
    ⨅ k : ℕ, originalBoundaryAscendingRankKernel (p := p) (q := q) J N k k ⊔ H := by
  calc
    _ = ⨅ k : ℕ, originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N k k :=
      doubleRank_residual_iInf_equal_orders (Over.mk p) x y σ N H
    _ = _ := by
      congr 1
      funext k
      exact congrArg (fun I ↦ I ⊔ H)
        (originalBoundaryDoubleRankKernel_eq_ascending_same_order J N k)

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A]

/-- Ascending support data gives one power and shared corrections on every bounded order box. -/
theorem originalBoundary_ascending_bounded_order_corrections
    (N r₀ s₀ : ℕ) (Q : Ideal R) (hfg : Q.FG)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r₀ s₀ ⊔ H).radical)
    (k : ℕ) :
    ∃ d : ℕ, ∀ a ∈ Q ^ d, ∃ b ∈ H,
      ∀ r s : ℕ, r ≤ k → s ≤ k → ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) =
          (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ b) := by
  let hp := originalBoundary_ascending_residual_powers_all_orders J N r₀ s₀ Q hfg h k k
  let d := hp.choose
  have hd := hp.choose_spec
  exact ⟨d, fun a ha ↦ originalBoundary_bounded_order_shared_correction J N k a (hd ha)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
