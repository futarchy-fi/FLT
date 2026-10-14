/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitRetainedHorizontalCyclicAction
public import FLT.Mazur.WeierstrassSmoothHorizontalPairExt

/-!
# The full actual action on every retained cyclic component

The comparison on the independently constructed horizontal residue source
extends across all smooth parameters and both projective endpoints.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth) (j : Fin (s + 1))
open WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "v" => positiveSplitCyclicSmoothGroupIso D s hk

/-- The actual action on each first-chain retained component is universal scaling. -/
theorem positiveSplitCoefficientAction_retainedFirstComponent :
    ((v).hom.hom.hom.hom ⊗ₘ Z ⟨j.val + 2, by omega⟩) ≫ B =
      ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨j.val + 2, by omega⟩ := by
  let _ : IsSeparated (finiteGlobalStructure hπ data (s + 1) hs) :=
    (finiteGlobalStructure_isProper hπ data (s + 1) hs).toIsSeparated
  let _ : IsSeparated (Over.mk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R 𝕂)))
        (finiteGlobalStructure hπ data (s + 1) hs))).hom := by
    change IsSeparated (pullback.fst _ _)
    infer_instance
  apply smoothHorizontalPair_hom_ext D _ _ true
  simpa only [Category.assoc] using
    splitRetainedHorizontalFirstCyclicAction_pair hπ data D s hs hstart hk hp j

/-- The actual action on each second-chain retained component is universal scaling. -/
theorem positiveSplitCoefficientAction_retainedSecondComponent :
    ((v).hom.hom.hom.hom ⊗ₘ Z ⟨2 * s + 4 - (j.val + 1), by omega⟩) ≫ B =
      ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨2 * s + 4 - (j.val + 1), by omega⟩ := by
  let _ : IsSeparated (finiteGlobalStructure hπ data (s + 1) hs) :=
    (finiteGlobalStructure_isProper hπ data (s + 1) hs).toIsSeparated
  let _ : IsSeparated (Over.mk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R 𝕂)))
        (finiteGlobalStructure hπ data (s + 1) hs))).hom := by
    change IsSeparated (pullback.fst _ _)
    infer_instance
  apply smoothHorizontalPair_hom_ext D _ _ false
  simpa only [Category.assoc] using
    splitRetainedHorizontalSecondCyclicAction_pair hπ data D s hs hstart hk hp j

end FLT.Mazur.WeierstrassDividedDepth
