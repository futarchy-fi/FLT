/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFramePositiveRank
public import FLT.Mazur.RelativeDoubleRankScalarKernels
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts

/-!
# Empty zero-rank stages of the full original relation

Reflexivity supplies a point in every original fiber. Every zero-rank
coefficient stage is consequently the empty scheme at every pair of orders.
Its exact scalar kernel is the unit ideal; no reduction is involved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance positiveOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance positiveOver_etale : Etale (Over.mk p).hom := ‹Etale p›
include e

/-- The actual identity arrow gives a one-frame at every original point. -/
theorem original_rankImage_one_eq_top : rankImageOpen (Over.mk p) 1 = ⊤ := by
  apply rankImageOpen_one_eq_top
  exact fun z ↦ ⟨e.r z, congrArg (fun f : A ⟶ A ↦ f z) e.reflexivity₁⟩

/-- Reflexivity excludes rank zero on the whole original base. -/
theorem original_exactRank_pos {z : A} {n : ℕ} (hz : z ∈ exactRank (Over.mk p) n) :
    0 < n := by
  apply exactRank_pos (Over.mk p) _ hz
  exact fun z ↦ ⟨e.r z, congrArg (fun f : A ⟶ A ↦ f z) e.reflexivity₁⟩

variable (x y : B ⟶ A) (n m r s : ℕ)

/-- A zero at either independent endpoint makes the entire thickening empty. -/
theorem original_doubleRank_zero_isEmpty (h : n = 0 ∨ m = 0) :
    IsEmpty (doubleRankThickening (Over.mk p) x y n m r s) := by
  refine ⟨fun z ↦ ?_⟩
  have hz := doubleRankMap_endpoints (Over.mk p) x y n m r s z
  rcases h with hn | hm
  · exact (Nat.ne_of_gt (original_exactRank_pos e hz.1)) hn
  · exact (Nat.ne_of_gt (original_exactRank_pos e hz.2)) hm

/-- The exact full coefficient kernel on a zero-rank chart is already the unit ideal. -/
theorem original_doubleRank_zero_kernel_top {R : Type} [CommRing R]
    (σ : R →+* Γ(B, ⊤)) (h : n = 0 ∨ m = 0) :
    doubleRankScalarKernel (Over.mk p) x y σ n m r s = ⊤ := by
  let _ := original_doubleRank_zero_isEmpty e x y n m r s h
  apply top_unique
  intro a _
  exact Subsingleton.elim _ _

end FLT.Mazur.EquivalenceRelationOrderedFrames
