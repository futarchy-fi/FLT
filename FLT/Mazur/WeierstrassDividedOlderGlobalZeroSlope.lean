/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalZeroBoundaries
public import FLT.Mazur.WeierstrassModificationXFiberExteriorGeometry

/-!
# The full punctured slope attachment in the retained global model

Both boundary maps use the same complete slope line with its two ordered
roots removed. Its actual global inclusion is exactly each full boundary
intersection and retains the original cubic contraction.
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
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
open WeierstrassModificationX
local notation "ha" => D.a₁_unit.map (residue R)
local notation "g" => olderGlobalZeroSuccessiveChart hπ data D j hj r hr hk0 hk
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The punctured slope line as the entire first horizontal boundary in the global fiber. -/
def olderGlobalZeroSlopeChart := fiberExteriorSlopeChart a c ≫ g

instance olderGlobalZeroSlopeChart_isOpenImmersion :
    IsOpenImmersion (olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The original map from the entire punctured slope line to the preceding exterior. -/
def olderGlobalZeroSlopeToExterior :=
  (fiberExteriorSlopeIso a c).hom ≫ olderGlobalZeroToExterior hπ data D j hj r hr hk0 hk

/-- The original map from the same punctured slope line to infinity. -/
def olderGlobalZeroSlopeToInfinity :=
  (fiberInfinitySlopeIso a c).hom ≫ olderGlobalZeroToInfinity hπ data D j hj r hr hk0 hk

/-- The punctured slope exterior map retains its actual global inclusion. -/
@[reassoc] theorem olderGlobalZeroSlopeToExterior_comp :
    olderGlobalZeroSlopeToExterior hπ data D j hj r hr hk0 hk ≫
      olderGlobalExteriorTensorChart hπ data K j hj r hr =
        olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroSlopeToExterior, Category.assoc, olderGlobalZeroToExterior_comp]
  rfl

/-- The punctured slope infinity map retains the same actual global inclusion. -/
@[reassoc] theorem olderGlobalZeroSlopeToInfinity_comp :
    olderGlobalZeroSlopeToInfinity hπ data D j hj r hr hk0 hk ≫
      finiteInfinityTensorChart hπ data K (j + 1 + r) hr =
        olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalZeroSlopeToInfinity, Category.assoc, olderGlobalZeroToInfinity_comp,
    ← Category.assoc, fiberInfinitySlopeIso_inclusion]
  rfl

/-- The entire punctured slope line is exactly the full exterior intersection. -/
theorem olderGlobalZeroSlopeChart_exterior_intersection :
    Set.range (olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk) =
      Set.range g ∩ Set.range (olderGlobalExteriorTensorChart hπ data K j hj r hr) := by
  change Set.range (g ∘ fiberExteriorSlopeChart a c) = _
  rw [Set.range_comp, fiberExteriorSlopeChart_range,
    ← olderGlobalZeroExterior_preimage hπ data D j hj r hr hk0 hk,
    Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The same punctured slope line is exactly the full infinity intersection. -/
theorem olderGlobalZeroSlopeChart_infinity_intersection :
    Set.range (olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk) =
      Set.range g ∩ Set.range (finiteInfinityTensorChart hπ data K (j + 1 + r) hr) := by
  change Set.range (g ∘ fiberExteriorSlopeChart a c) = _
  rw [Set.range_comp, fiberExteriorSlopeChart_range,
    ← fiberExterior_infinity_open a c,
    ← olderGlobalZeroInfinity_preimage hπ data D j hj r hr hk0 hk,
    Set.image_preimage_eq_inter_range, Set.inter_comm]

/-- The global slope chart keeps the restriction of every original cubic function. -/
@[reassoc] theorem olderGlobalZeroSlopeChart_toCurve :
    olderGlobalZeroSlopeChart hπ data D j hj r hr hk0 hk ≫
      pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr) ≫
        finiteGlobalContraction hπ data (j + 1 + r) hr =
      fiberExteriorSlopeChart a c ≫ Spec.map (CommRingCat.ofHom
        (globalZeroSuccessiveContraction hπ data D j hj hk0 hk).toRingHom) ≫ toCurve d := by
  rw [olderGlobalZeroSlopeChart, Category.assoc, olderGlobalZeroSuccessiveChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
