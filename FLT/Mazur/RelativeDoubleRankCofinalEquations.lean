/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankTransitionNaturality
public import FLT.Mazur.RelativeDoubleRankCompleteKernel

/-!
# Exact scalar equations along cofinal rank orders

The constructed transitions restrict full equations from larger orders.
Equal orders are cofinal among independent orders for exact kernels, including
kernels with a fixed residual ideal added. This does not interchange infinite
intersection with ideal sum or construct one correction valid at all orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S)

/-- Full equations at equal orders suffice at every independent pair of orders. -/
theorem doubleRank_sections_iff_equal_orders (n m : ℕ) (a b : Γ(B, ⊤)) :
    (∀ r s : ℕ, (doubleRankMap E x y n m r s).appTop a =
      (doubleRankMap E x y n m r s).appTop b) ↔
    ∀ k : ℕ, (doubleRankMap E x y n m k k).appTop a =
      (doubleRankMap E x y n m k k).appTop b := by
  refine ⟨fun h k ↦ h k k, fun h r s ↦ ?_⟩
  exact doubleRankTransition_section_eq E x y n m (le_max_left r s)
    (le_max_right r s) a b (h (max r s))

variable {R : Type} [CommRing R] (σ : R →+* Γ(B, ⊤))

/-- Higher orders impose stronger exact original scalar equations. -/
theorem doubleRankScalarKernel_antitone (n m : ℕ) {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankScalarKernel E x y σ n m r' s' ≤
      doubleRankScalarKernel E x y σ n m r s := by
  intro a ha
  change (doubleRankMap E x y n m r' s').appTop (σ a) = 0 at ha
  have he : (doubleRankMap E x y n m r' s').appTop (σ a) =
      (doubleRankMap E x y n m r' s').appTop 0 := by
    simpa only [map_zero] using ha
  have h := doubleRankTransition_section_eq E x y n m hr hs (σ a) 0 he
  simpa only [doubleRankScalarKernel, RingHom.mem_ker, RingHom.comp_apply, map_zero] using h

/-- A complete finite rectangle restricts exactly along both order increases. -/
theorem doubleRankCompleteKernel_antitone (N : ℕ) {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankCompleteKernel E x y σ N r' s' ≤
      doubleRankCompleteKernel E x y σ N r s := by
  apply iInf_mono
  intro i
  exact doubleRankScalarKernel_antitone E x y σ i.1.val i.2.val hr hs

/-- The full off-diagonal kernel also restricts exactly, retaining all its equations. -/
theorem doubleRankCollisionKernel_antitone (N : ℕ) {r s r' s' : ℕ}
    (hr : r ≤ r') (hs : s ≤ s') :
    doubleRankCollisionKernel E x y σ N r' s' ≤
      doubleRankCollisionKernel E x y σ N r s := by
  apply iInf_mono
  intro n
  apply iInf_mono
  intro m
  apply iInf_mono
  intro _
  exact doubleRankScalarKernel_antitone E x y σ n.val m.val hr hs

/-- Residual exact equations at all orders can be tested on the equal-order sequence. -/
theorem doubleRank_residual_iInf_equal_orders (N : ℕ) (H : Ideal R) :
    (⨅ r : ℕ, ⨅ s : ℕ, doubleRankCollisionKernel E x y σ N r s ⊔ H) =
      ⨅ k : ℕ, doubleRankCollisionKernel E x y σ N k k ⊔ H := by
  apply le_antisymm
  · exact le_iInf fun k ↦ (iInf_le _ k).trans (iInf_le _ k)
  · refine le_iInf fun r ↦ le_iInf fun s ↦ ?_
    exact (iInf_le _ (max r s)).trans (sup_le_sup_right
      (doubleRankCollisionKernel_antitone E x y σ N (le_max_left r s) (le_max_right r s)) H)

end FLT.Mazur.RelativeOrderedTuples
