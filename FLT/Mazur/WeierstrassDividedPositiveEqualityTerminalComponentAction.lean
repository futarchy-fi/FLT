/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalHorizontalCyclicAction
public import FLT.Mazur.WeierstrassSmoothHorizontalPairExt

/-!
# The full actual action on the terminal cyclic component

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
  (hp : 2 * (start + s + 1) = depth)
open WeierstrassIntegralChart
local notation "𝕂" => ResidueField R
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs 𝕂
local notation "v" => positiveEqualityCyclicSmoothGroupIso D s hk

/-- The actual action on the terminal component is universal scaling. -/
theorem positiveEqualityCoefficientAction_terminalComponent :
    ((v).hom.hom.hom.hom ⊗ₘ Z ⟨s + 2, by omega⟩) ≫ B =
      ProjectiveLineUniversalAction.act 𝕂 ≫ Z ⟨s + 2, by omega⟩ := by
  let _ : IsSeparated (finiteGlobalStructure hπ data (s + 1) hs) :=
    (finiteGlobalStructure_isProper hπ data (s + 1) hs).toIsSeparated
  let _ : IsSeparated (Over.mk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R 𝕂)))
        (finiteGlobalStructure hπ data (s + 1) hs))).hom := by
    change IsSeparated (pullback.fst _ _)
    infer_instance
  apply smoothHorizontalPair_hom_ext D _ _ true
  simpa only [Category.assoc] using
    terminalHorizontalCyclicAction_pair hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
