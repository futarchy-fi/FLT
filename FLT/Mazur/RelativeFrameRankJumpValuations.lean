/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameExactRank
public import FLT.Mazur.NoetherianClosedImageGenerizations
public import FLT.Mazur.SchemeValuationImageClosure

/-!
# Actual larger-frame valuations at residual rank points

Failure of an original open rank bound is witnessed by a larger original
frame specializing to that point. If the center has exact rank n, its
(n+1)-frame valuation square cannot extend. The witness uses the full original
frame scheme, with its exact original center.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [NoetherianSpace S]

/-- Approaching frame images have an actual original frame over a generization of the center. -/
theorem mem_closure_rankImage_iff (n : ℕ) (x : S) :
    x ∈ closure (rankImageOpen E n : Set S) ↔
      ∃ y : (distinctScheme E (Fin n)).left, (distinctScheme E (Fin n)).hom y ⤳ x := by
  let _ := (rankImageOpen E n).ι.isOpenEmbedding.isInducing.noetherianSpace
  have h := NoetherianClosedImage.mem_closure_image_iff
    (rankImageOpen E n).ι (rankImageOpen E n).ι.continuous isClosed_univ x
  rw [Set.image_univ, Scheme.Opens.range_ι] at h
  rw [h]
  constructor
  · rintro ⟨z, _, hz⟩
    obtain ⟨y, hy⟩ := z.property
    exact ⟨y, hy ▸ hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨_, Set.mem_range_self y⟩, trivial, hy⟩

/-- The open rank bound is exactly absence of larger frames over any generization. -/
theorem mem_rankBound_iff_no_specializing_frame (n : ℕ) (x : S) :
    x ∈ rankBoundOpen E n ↔
      ∀ y : (distinctScheme E (Fin (n + 1))).left,
        ¬ (distinctScheme E (Fin (n + 1))).hom y ⤳ x := by
  change (¬ x ∈ closure (rankImageOpen E (n + 1) : Set S)) ↔ _
  rw [mem_closure_rankImage_iff]
  exact not_exists

/-- A rank jump supplies a valuation square at the unchanged original point. -/
theorem exists_rankJump_square (n : ℕ) (x : S) (hx : x ∉ rankBoundOpen E n) :
    ∃ V : ValuativeCommSq (distinctScheme E (Fin (n + 1))).hom,
      V.i₂ (closedPoint V.R) = x := by
  have hc : x ∈ closure (rankImageOpen E (n + 1) : Set S) := not_not.mp hx
  obtain ⟨y, hy⟩ := (mem_closure_rankImage_iff E (n + 1) x).mp hc
  obtain ⟨V, _, hV⟩ := SchemeSpecializationValuation.exists_square _ y x hy
  exact ⟨V, hV⟩

omit [NoetherianSpace S] in
/-- At an exact rank-n center every larger-frame valuation witness fails to extend. -/
theorem rankJump_square_no_lift (n : ℕ) (x : S) (hx : x ∈ rankAtMost E n)
    (V : ValuativeCommSq (distinctScheme E (Fin (n + 1))).hom)
    (hV : V.i₂ (closedPoint V.R) = x) : ¬ V.commSq.HasLift := by
  apply SchemeSpecializationValuation.no_lift_of_fiber_disjoint _ isClosed_univ V (by trivial)
  intro y _ hy
  apply hx
  exact ⟨y, hy.trans hV⟩

/-- Residual exact-rank points have actual nonextendible larger-frame squares. -/
theorem exists_rankJump_square_no_lift (n : ℕ) (x : S)
    (hx : x ∈ exactRank E n) (ho : x ∉ rankBoundOpen E n) :
    ∃ V : ValuativeCommSq (distinctScheme E (Fin (n + 1))).hom,
      V.i₂ (closedPoint V.R) = x ∧ ¬ V.commSq.HasLift := by
  obtain ⟨V, hV⟩ := exists_rankJump_square E n x ho
  exact ⟨V, hV, rankJump_square_no_lift E n x hx.2 V hV⟩

variable [QuasiCompact E.hom]

/-- A failed rank bound increases the exact original rank along an actual specialization. -/
theorem exists_larger_exactRank_specialization (n : ℕ) (x : S)
    (hx : x ∉ rankBoundOpen E n) :
    ∃ (m : ℕ) (y : S), n < m ∧ y ∈ exactRank E m ∧ y ⤳ x := by
  obtain ⟨V, hV⟩ := exists_rankJump_square E n x hx
  let y := (distinctScheme E (Fin (n + 1))).hom (V.i₁ default)
  obtain ⟨m, hm⟩ := exists_point_rank E y
  have hnm : n + 1 ≤ m := (hm (n + 1)).mp ⟨V.i₁ default, rfl⟩
  refine ⟨m, y, hnm, ⟨(hm m).mpr le_rfl, ?_⟩, ?_⟩
  · exact fun h ↦ Nat.not_succ_le_self m ((hm (m + 1)).mp h)
  · rw [← hV]
    exact SchemeSpecializationValuation.square_specializes _ V

end FLT.Mazur.RelativeOrderedTuples
