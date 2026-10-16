/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeExactRankFrameCover
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Constructed infinitesimal thickenings of every exact original rank stratum

Inside the original n-frame image open, take every positive power of the
vanishing ideal of the closed rank bound. All stages have the exact rank
support. Their full quotient scheme structures are retained in splitting covers.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] (n : ℕ)

/-- The exact rank piece as a closed set inside the original frame-image open. -/
def rankStratumClosed : Closeds (rankImageOpen E n).toScheme :=
  ⟨(rankImageOpen E n).ι ⁻¹' rankAtMost E n,
    (rankAtMost_isClosed E n).preimage (rankImageOpen E n).ι.continuous⟩

/-- The canonical defining ideal on the original rank-image open. -/
def rankStratumIdeal : (rankImageOpen E n).toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (rankStratumClosed E n)

/-- Every positive ideal power gives an actual scheme, not only a support set. -/
def rankThickening (k : ℕ) : Scheme := (rankStratumIdeal E n ^ (k + 1)).subscheme

/-- The stage retains its original locally closed map into the base. -/
def rankThickeningMap (k : ℕ) : rankThickening E n k ⟶ S :=
  (rankStratumIdeal E n ^ (k + 1)).subschemeι ≫ (rankImageOpen E n).ι

omit [QuasiCompact E.hom] in
/-- All infinitesimal stages cover exactly the full original rank piece. -/
theorem rankThickeningMap_range (k : ℕ) :
    Set.range (rankThickeningMap E n k) = exactRank E n := by
  change Set.range ((rankStratumIdeal E n ^ (k + 1)).subschemeι ≫ _) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι]
  rw [Scheme.IdealSheafData.support_pow_succ]
  change (rankImageOpen E n).ι ''
    ((rankStratumClosed E n : Closeds _) : Set _) = exactRank E n
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hb⟩
    exact ⟨⟨x, hx⟩, hb, rfl⟩

omit [QuasiCompact E.hom] in
/-- Each stage has a constructed surjective etale cover by original complete frames. -/
theorem rankThickening_frameCover_surjective (k : ℕ) :
    Function.Surjective (rankFrameProjection E n (rankThickeningMap E n k)) :=
  rankFrameProjection_surjective E n _ (rankThickeningMap_range E n k).le

/-- The full original source splits on that cover with all stage coefficients intact. -/
def rankThickeningSplitIso (k : ℕ) :
    (∐ fun _ : Fin n ↦ rankFrameCover E n (rankThickeningMap E n k)) ≅
      pullback E.hom
        (rankFrameProjection E n (rankThickeningMap E n k) ≫ rankThickeningMap E n k) :=
  rankFrameCoverIso E n _ (rankThickeningMap_range E n k).le

/-- Every original point, including residual points, occurs on some rank thickening. -/
theorem exists_rankThickening_lift (x : S) (k : ℕ) :
    ∃ (n : ℕ) (y : rankThickening E n k), rankThickeningMap E n k y = x := by
  obtain ⟨n, hn⟩ := exists_exactRank E x
  rw [← rankThickeningMap_range E n k] at hn
  obtain ⟨y, hy⟩ := hn
  exact ⟨n, y, hy⟩

end FLT.Mazur.RelativeOrderedTuples
