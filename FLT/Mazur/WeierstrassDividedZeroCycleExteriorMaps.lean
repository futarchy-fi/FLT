/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleExteriorExt

/-!
# Cyclic family maps on infinity and the redundant initial chart

The full infinity chart factors through the normalized exterior component.
The original slope transition supplies the initial chart map and compatibility.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "ι" => zeroRetainedExteriorInfinityChart hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "E" => zeroRetainedExteriorOrientedIso hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "J" => initialZeroSlopeAtlasIso hπ data D (by omega) hstart (s + 1) hs
local notation "q" => initialZeroToTensorInfinity hπ data D (by omega) hstart (s + 1) hs

/-- The original initial atlas object maps wholly into the unchanged infinity atlas object. -/
def zeroSplitCycleInitialToInfinity :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ⟶
      globalTensorAtlasObject hπ data K (s + 1) hs 0 :=
  (J).inv ≫ q

/-- The factorization preserves the original global atlas maps as scheme morphisms. -/
@[reassoc] theorem zeroSplitCycleInitialToInfinity_global :
    zeroSplitCycleInitialToInfinity hπ data D s hs hstart hk ≫
        globalTensorAtlasMap hπ data K (s + 1) hs 0 =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ := by
  apply (cancel_epi (J).hom).mp
  simp only [zeroSplitCycleInitialToInfinity, Category.assoc, Iso.hom_inv_id_assoc]
  change q ≫ finiteInfinityTensorChart hπ data K (s + 1) hs =
    (J).hom ≫ globalTensorAtlasMap hπ data K (s + 1) hs
      (Fin.succ ⟨s + 1 + 1, by omega⟩)
  rw [initialZeroToTensorInfinity_chart, initialZeroSlopeAtlasIso_map]

variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))

/-- The exterior member of the family supplies the entire infinity chart map. -/
def zeroSplitCycleInfinityDesc : globalTensorAtlasObject hπ data K (s + 1) hs 0 ⟶ Y :=
  ι ≫ (E).hom ≫ F 0

/-- The redundant initial chart is assigned the restriction through its actual transition. -/
def zeroSplitCycleInitialDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ⟶ Y :=
  zeroSplitCycleInitialToInfinity hπ data D s hs hstart hk ≫
    zeroSplitCycleInfinityDesc hπ data D s hs hstart hk F

/-- The two chosen maps agree along the full original initial-to-infinity transition. -/
@[reassoc] theorem zeroSplitCycleInitialToInfinity_desc :
    zeroSplitCycleInitialToInfinity hπ data D s hs hstart hk ≫
        zeroSplitCycleInfinityDesc hπ data D s hs hstart hk F =
      zeroSplitCycleInitialDesc hπ data D s hs hstart hk F := rfl

/-- The normalized slope chart restriction is the unchanged original infinity transition. -/
@[reassoc] theorem zeroSplitCycleInitialDesc_slope :
    (J).hom ≫ zeroSplitCycleInitialDesc hπ data D s hs hstart hk F =
      q ≫ zeroSplitCycleInfinityDesc hπ data D s hs hstart hk F := by
  simp only [zeroSplitCycleInitialDesc, zeroSplitCycleInitialToInfinity,
    Category.assoc, Iso.hom_inv_id_assoc]

/-- Every common scheme over the two atlas maps sees equal descended morphisms. -/
theorem zeroSplitCycleExteriorDesc_compatible {V : Scheme.{u}}
    (a : V ⟶ globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 3, by omega⟩)
    (b : V ⟶ globalTensorAtlasObject hπ data K (s + 1) hs 0)
    (w : a ≫ globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ =
      b ≫ globalTensorAtlasMap hπ data K (s + 1) hs 0) :
    a ≫ zeroSplitCycleInitialDesc hπ data D s hs hstart hk F =
      b ≫ zeroSplitCycleInfinityDesc hπ data D s hs hstart hk F := by
  have h : a ≫ zeroSplitCycleInitialToInfinity hπ data D s hs hstart hk = b := by
    apply (cancel_mono (globalTensorAtlasMap hπ data K (s + 1) hs 0)).mp
    simpa only [Category.assoc, zeroSplitCycleInitialToInfinity_global] using w
  simp only [zeroSplitCycleInitialDesc, ← Category.assoc, h]

end FLT.Mazur.WeierstrassDividedDepth
