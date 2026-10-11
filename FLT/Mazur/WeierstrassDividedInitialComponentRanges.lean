/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialProjectiveComponents
public import FLT.Mazur.WeierstrassDividedAdjacentComponentRanges

/-!
# Complete images of the two initial projective components

Both full conic parameters and the entire first retained lines occur in the
initial component images. Their union retains the whole original initial conic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- An isomorphism of source schemes preserves every point in a component image. -/
theorem initialComponent_iso_comp_range {A B X : Scheme.{u}} (e : A ≅ B) (f : B ⟶ X) :
    Set.range (e.hom ≫ f) = Set.range f :=
  e.hom.homeomorph.surjective.range_comp f

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (r : ℕ) (hr : 1 + r ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "E" => conicZeroAffineIso c hc
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "P₁" => initialGlobalConicFirstParameter hπ data D (1 + r) hr hstart (by omega)
local notation "P₂" => initialGlobalConicSecondParameter hπ data D (1 + r) hr hstart (by omega)
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D 0 h1 r hr hstart hk
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D 0 h1 r hr hstart hk

/-- The complete first initial component contains both original affine pieces. -/
theorem initialGlobalFirstComponent_range :
    Set.range (initialGlobalFirstComponent hπ data D h1 hstart hk r hr) =
      Set.range P₁ ∪ Set.range G₁ := by
  rw [ProjectiveLine.map_range, initialGlobalFirstComponent_left,
    initialGlobalFirstComponent_right, adjacentChartScaling_range]
  congr 1
  exact initialComponent_iso_comp_range E P₁

/-- The complete second initial component contains both original affine pieces. -/
theorem initialGlobalSecondComponent_range :
    Set.range (initialGlobalSecondComponent hπ data D h1 hstart hk r hr) =
      Set.range P₂ ∪ Set.range G₂ := by
  rw [ProjectiveLine.map_range, initialGlobalSecondComponent_left,
    initialGlobalSecondComponent_right, adjacentChartScaling_range]
  congr 1
  exact initialComponent_iso_comp_range E P₂

/-- Both full initial components contain exactly the initial conic and the next two lines. -/
theorem initialGlobalComponents_conic_range :
    Set.range (initialGlobalFirstComponent hπ data D h1 hstart hk r hr) ∪
        Set.range (initialGlobalSecondComponent hπ data D h1 hstart hk r hr) =
      Set.range (initialGlobalConic hπ data D (1 + r) hr hstart (by omega)) ∪
        (Set.range G₁ ∪ Set.range G₂) := by
  rw [initialGlobalFirstComponent_range, initialGlobalSecondComponent_range,
    Set.union_union_union_comm, initialGlobalConicParameters_cover]

/-- The original initial conic is covered by the two complete initial components. -/
theorem initialGlobalComponents_cover_conic :
    Set.range (initialGlobalConic hπ data D (1 + r) hr hstart (by omega)) ⊆
      Set.range (initialGlobalFirstComponent hπ data D h1 hstart hk r hr) ∪
        Set.range (initialGlobalSecondComponent hπ data D h1 hstart hk r hr) :=
  Set.subset_union_left.trans
    (le_of_eq (initialGlobalComponents_conic_range hπ data D h1 hstart hk r hr).symm)

end FLT.Mazur.WeierstrassDividedDepth
