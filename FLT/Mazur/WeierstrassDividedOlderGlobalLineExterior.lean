/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior
public import FLT.Mazur.WeierstrassSuccessiveXResidueLineHorizontal

/-!
# Full ordered line intersections with the retained preceding exterior

Each complete punctured horizontal line is the actual scheme intersection
with the preceding exterior in every later global model. Both Laurent
parameters and all global inclusion maps remain the original ones.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "i" => olderGlobalExteriorTensorChart hπ data K j hj r hr
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
local notation "p" => ProjectiveLine.overlapLeft K
local notation "L" => residueSuccessiveLineImmersion D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "l" => residueLineToHorizontal D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
variable (s : ResidueField R) (hs : s * (s + residue R W.a₁) = 0)

/-- The punctured horizontal line maps into the actual retained preceding exterior. -/
def olderGlobalLineToExterior :=
  l s hs ≫ olderGlobalHorizontalToExterior hπ data K j hj r hr

/-- This attachment retains its actual global line inclusion. -/
@[reassoc] theorem olderGlobalLineToExterior_comp :
    olderGlobalLineToExterior hπ data D j hj r hr hk0 hk s hs ≫ i = p ≫ L s hs ≫ g := by
  rw [olderGlobalLineToExterior, Category.assoc, olderGlobalHorizontalToExterior_comp,
    ← Category.assoc, residueLineToHorizontal_comp, Category.assoc]

/-- The whole punctured line is the full global intersection with the preceding exterior. -/
theorem olderGlobalLineExterior_isPullback :
    IsPullback (olderGlobalLineToExterior hπ data D j hj r hr hk0 hk s hs) p i (L s hs ≫ g) :=
  (residueLineHorizontal_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) s hs).paste_horiz
      (olderGlobalExteriorTensor_isPullback hπ data K j hj r hr)

/-- No additional line points enter the preceding exterior after later modifications. -/
theorem olderGlobalLineExterior_preimage :
    (L s hs ≫ g) ⁻¹' Set.range i = Set.range p := by
  change (L s hs) ⁻¹' (g ⁻¹' Set.range i) = _
  rw [olderGlobalExteriorTensor_preimage]
  exact residueLineHorizontal_preimage D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) s hs

/-- The original zero-slope line keeps its complete punctured intersection globally. -/
theorem olderGlobalFirstLineExterior_isPullback :
    IsPullback (olderGlobalLineToExterior hπ data D j hj r hr hk0 hk 0 (by simp)) p i
      (olderGlobalMiddleFirstLine hπ data D j hj r hr hk0 hk) :=
  olderGlobalLineExterior_isPullback hπ data D j hj r hr hk0 hk 0 (by simp)

/-- The opposite line keeps the same full intersection with its original tangent ordering. -/
theorem olderGlobalSecondLineExterior_isPullback :
    IsPullback (olderGlobalLineToExterior hπ data D j hj r hr hk0 hk
      (-residue R W.a₁) (by simp)) p i
        (olderGlobalMiddleSecondLine hπ data D j hj r hr hk0 hk) :=
  olderGlobalLineExterior_isPullback hπ data D j hj r hr hk0 hk (-residue R W.a₁) (by simp)

end FLT.Mazur.WeierstrassDividedDepth
