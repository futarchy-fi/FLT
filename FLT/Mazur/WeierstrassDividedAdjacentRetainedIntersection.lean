/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentRetainedIntegral
public import FLT.Mazur.WeierstrassDividedExteriorIntersections

/-!
# The full adjacent chart intersection after every later retention

The original common boundary is the whole scheme intersection of adjacent
retained charts. This follows from the defining exterior pushout and stays
cartesian through every later open inclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0)

/-- Two successive original x-charts intersect in exactly their common divided boundary. -/
theorem Exterior.adjacent_isPullback {k : ℕ} {d : Data W π k}
    (E : Exterior d) (e : Data W π (k + 1)) (fData : Data W π (k + 1 + 1)) :
    IsPullback (nextToX e) (previousToX hπ e fData)
      (E.newX hπ e ≫ (E.advance hπ e).retained hπ fData)
      ((E.advance hπ e).newX hπ fData) := by
  have H : IsPullback (nextToX e) (𝟙 (boundary e))
      (E.newX hπ e) (E.advance hπ e).attach :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp]; rfl⟩
  simpa only [Category.id_comp] using
    H.paste_vert ((E.advance hπ e).retained_newX_isPullback hπ fData)

variable {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "tail" => finiteStageRetained hπ data (j + 2) hjNext r hr ≫
  Exterior.exteriorChart (finiteExterior hπ data E₀ (j + 2 + r) hr)
local notation "old" => adjacentRetainedOldChart hπ data j hj r hr
local notation "next" => olderSuccessiveChart hπ data (j + 1) hjNext r hr

/-- No further points enter the adjacent chart intersection during later retention. -/
theorem adjacentRetainedIntegral_isPullback :
    IsPullback (nextToX e) (previousToX hπ e fData) old next := by
  rw [adjacentRetainedOldChart_eq hπ data j hj hjNext r hr]
  change IsPullback (nextToX e) (previousToX hπ e fData)
    ((E).newX hπ e ≫ (Exterior.advance hπ (E) e).retained hπ fData ≫ tail)
    ((Exterior.advance hπ (E) e).newX hπ fData ≫ tail)
  have H := Exterior.adjacent_isPullback hπ (E) e fData
  have H' : IsPullback (nextToX e) (previousToX hπ e fData)
      (((E).newX hπ e ≫ (Exterior.advance hπ (E) e).retained hπ fData) ≫ tail)
      ((Exterior.advance hπ (E) e).newX hπ fData ≫ tail) :=
    IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ tail H.cone H.isLimit)
  simpa only [Category.assoc] using H'

/-- The actual retained adjacent fiber product is the original complete divided boundary. -/
def adjacentRetainedIntegralPullbackIso : boundary e ≅ pullback old next :=
  (adjacentRetainedIntegral_isPullback hπ data j hj hjNext r hr).isoPullback

/-- The full intersection comparison retains the original next-boundary projection. -/
@[reassoc] theorem adjacentRetainedIntegralPullbackIso_old :
    (adjacentRetainedIntegralPullbackIso hπ data j hj hjNext r hr).hom ≫
      pullback.fst old next = nextToX e :=
  (adjacentRetainedIntegral_isPullback hπ data j hj hjNext r hr).isoPullback_hom_fst

/-- The full intersection comparison retains the original preceding-boundary projection. -/
@[reassoc] theorem adjacentRetainedIntegralPullbackIso_next :
    (adjacentRetainedIntegralPullbackIso hπ data j hj hjNext r hr).hom ≫
      pullback.snd old next = previousToX hπ e fData :=
  (adjacentRetainedIntegral_isPullback hπ data j hj hjNext r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
