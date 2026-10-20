/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalNumeratorTower
public import FLT.Mazur.RankStageGlobalKernelLocalization

/-!
# Coherent global homogeneous numerators on the actual rank stage

For finitely many compatible homogeneous core towers, construct one monotone
exponent sequence and global homogeneous numerators with exact rescaled
transition equations at every pair of orders. The stage may be nonaffine.
A uniform bound and unscaled overlap splitting are not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem rescaled_all_orders {R : ℕ → Type*} [∀ k, CommRing (R k)]
    (ρ : ∀ k l, k ≤ l → R l →+* R k)
    (hρ : ∀ k z, ρ k k (le_refl k) z = z)
    (hcomp : ∀ k l m (h : k ≤ l) (h' : l ≤ m) z,
      ρ k l h (ρ l m h' z) = ρ k m (h.trans h') z)
    (r : ∀ k, R k) (hr : ∀ k l (h : k ≤ l), ρ k l h (r l) = r k)
    (N : ℕ → ℕ) (hN : Monotone N) (w : ∀ k, R k)
    (hs : ∀ k, ρ k (k + 1) (Nat.le_succ k) (w (k + 1)) =
      r k ^ (N (k + 1) - N k) * w k) :
    ∀ k l (h : k ≤ l), ρ k l h (w l) = r k ^ (N l - N k) * w k := by
  intro k l h
  induction l, h using Nat.le_induction with
  | base => rw [hρ, Nat.sub_self, pow_zero, one_mul]
  | succ l h ih =>
    rw [← hcomp k l (l + 1) h (Nat.le_succ l), hs, map_mul, map_pow, hr, ih,
      ← mul_assoc, ← pow_add]
    have h₁ : N k ≤ N l := hN h
    have h₂ : N l ≤ N (l + 1) := hN (Nat.le_succ l)
    congr 2
    omega

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance rescaledOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rescaledOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rescaledOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (C : Finset (Γ(A, ⊤) × Γ(A, ⊤)))
  (hC : ∀ c : C, A.basicOpen c.val.1 ≤ rankImageOpen (Over.mk p) n)
  (hc : ∀ k, (⨆ c : C, rankStageCore e n c.val.1 (hC c) k) = ⊤)
  (J : A.IdealSheafData) {ι : Type*} [Finite ι]
  (a : ι → Γ(A, ⊤)) (ha : ∀ j, A.basicOpen (a j) ≤ rankImageOpen (Over.mk p) n)
local notation "r" j:max k:max => rankStageNormParameter e n C hC hc (a j) k
local notation "F" j:max k:max => rankStageGlobalCoreRestriction e n (a j) (ha j) k
attribute [local irreducible] rankStageCore rankStageNormParameter
  rankStageInvariantTransition rankStageGlobalCoreRestriction rankStageCoreRestriction

/-- All actual finite core errors have global homogeneous numerators coherent up to powers. -/
theorem exists_rankStage_rescaled_global_kernel_towers
    (v : ∀ j k, rankStageCoreInvariants e n (a j) (ha j) k)
    (hv : ∀ j k, (rankStageCoreBoundaryIdeal e n (a j) (ha j) J k).subschemeι.appTop
      (v j k).val = 0)
    (ht : ∀ j k l (h : k ≤ l), rankStageCoreRestriction e n (a j) (ha j) h (v j l) = v j k) :
    ∃ (N : ℕ → ℕ) (w : ∀ k, ι → rankStageInvariants e n k), Monotone N ∧
      (∀ k j, w k j ∈ rankStageGlobalBoundaryKernel e n J k) ∧
      (∀ k j, (F j k) (w k j) = ((F j k) (r j k)) ^ N k * v j k) ∧
      ∀ k l (h : k ≤ l) j, rankStageInvariantTransition e n h (w l j) =
        (r j k) ^ (N l - N k) * w k j := by
  have hr (j : ι) (k l : ℕ) (h : k ≤ l) :
      rankStageInvariantTransition e n h (r j l) = r j k :=
    by
      apply Subtype.ext
      rw [rankStageInvariantTransition_val]
      exact rankStageNormParameter_transition e n C hC hc (a j) h
  obtain ⟨N, w, hN, hw, he, hs⟩ := FinitePrincipalNumeratorTower.exists_rescaled_tower
    (fun j k ↦ F j k) (fun _ k ↦ rankStageInvariantTransition e n (Nat.le_succ k))
    (fun j k ↦ rankStageCoreRestriction e n (a j) (ha j) (Nat.le_succ k))
    (fun j _ z ↦ rankStageGlobalCoreRestriction_transition e n (a j) (ha j) _ z)
    (fun j k ↦ r j k) (fun j k ↦ hr j k (k + 1) (Nat.le_succ k)) v
    (fun j k ↦ ht j k (k + 1) (Nat.le_succ k))
    (fun _ k ↦ rankStageGlobalBoundaryKernel e n J k)
    (fun j k b d h ↦ rankStageGlobalCoreRestriction_power_eq e n (a j) (ha j)
      C hC hc k b d h)
    (fun j k ↦ exists_rankStageGlobalBoundaryKernel_numerator e n (a j) (ha j)
      J C hC hc k (v j k) (hv j k))
  have hρ (k : ℕ) (z : rankStageInvariants e n k) :
      rankStageInvariantTransition e n (le_refl k) z = z := by
    have hm : rankStageTransition (Over.mk p) n (le_refl k) = 𝟙 _ := by
      apply (cancel_mono (rankThickeningMap (Over.mk p) n k)).mp
      rw [rankStageTransition_map, Category.id_comp]
    apply Subtype.ext
    rw [rankStageInvariantTransition_val, hm]
    rfl
  have hcomp (k l m : ℕ) (h : k ≤ l) (h' : l ≤ m) (z : rankStageInvariants e n m) :
      rankStageInvariantTransition e n h (rankStageInvariantTransition e n h' z) =
        rankStageInvariantTransition e n (h.trans h') z :=
    DFunLike.congr_fun (rankStageInvariantTransition_comp e n h h') z
  refine ⟨N, w, hN, hw, he, fun k l h j ↦ ?_⟩
  exact rescaled_all_orders (fun _ _ h ↦ rankStageInvariantTransition e n h) hρ hcomp
    (fun k ↦ r j k) (hr j) N hN (fun k ↦ w k j) (fun k ↦ hs k j) k l h

end FLT.Mazur.EquivalenceRelationOrderedFrames
