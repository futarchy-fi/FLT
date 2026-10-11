/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCyclicTorusAction
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientOverAction
public import FLT.Mazur.ProjectiveLineProductTorusRestriction
public import FLT.Mazur.PolygonSplitIdentityGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# The actual action on the complete exterior normalization component

The reciprocal identity-torus comparison extends across zero and infinity by
separatedness. The result concerns the actual specialized integral action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
open WeierstrassIntegralChart CartesianMonoidalCategory
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "G" => PolygonSplitGroup.model K (2 * s + 4)
local notation "M" => positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp


local notation "U" => MultiplicativeGroupScheme.gm K
local notation "c" => PolygonSplitGroup.component K (2 * s + 4) 0
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk
local notation "A" => positiveEqualityCycleAction hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs K
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "t" => PolygonPinching.torusToComponent K

/-- The actual action and polygon action coincide on the universal cyclic zero-torus pair. -/
theorem positiveEqualityCycleAction_zeroTorus :
    ((v).hom.hom.hom.hom ⊗ₘ (c ≫ M)) ≫ B = (c ⊗ₘ (c ≫ M)) ≫ A := by
  have h := positiveEqualityCycleAction_zeroTorusPoint hπ data D s hs hstart hk hp (U ⊗ U)
    (fst U U ≫ (v).hom.hom.hom.hom) (snd U U)
  rw [Category.assoc, positiveEqualityCyclicSmoothGroupIso_inclusion,
    ← finiteGlobalCoefficientOverAction_points] at h
  simpa only [lift_fst_comp_snd_comp] using h.symm

/-- The cyclic zero torus is the puncture of the original exterior normalization component. -/
@[reassoc] theorem positiveEqualityCycleSmoothMap_zeroComponent : c ≫ M = t ≫ Z 0 := by
  simpa only [map_zero] using
    positiveEqualityCycleSmoothMap_component hπ data D s hs hstart hk hp 0

/-- Agreement extends to the entire exterior component, including its two boundary points. -/
theorem positiveEqualityCycleAction_exterior :
    ((v).hom.hom.hom.hom ⊗ₘ Z 0) ≫ B = (c ⊗ₘ Z 0) ≫ A := by
  let _ : IsSeparated (finiteGlobalStructure hπ data (s + 1) hs) :=
    (finiteGlobalStructure_isProper hπ data (s + 1) hs).toIsSeparated
  let _ : IsSeparated (Over.mk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
        (finiteGlobalStructure hπ data (s + 1) hs))).hom := by
    change IsSeparated (pullback.fst _ _)
    infer_instance
  apply ProjectiveLineProductCharts.product_hom_ext_torus K (LaurentPolynomial K)
  rw [whiskerLeft_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    ← positiveEqualityCycleSmoothMap_zeroComponent]
  exact positiveEqualityCycleAction_zeroTorus hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
