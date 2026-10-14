/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassHorizontalLaurentBranches
public import FLT.Mazur.PrincipalOpenTensorRestriction

/-!
# Retained Laurent branches preserve the original divided functions

The normalization square commutes on every original tensor function. Thus
both retained punctures include into the original divided chart as the same
ordered node branches used by the arithmetic specialization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Equal-denominator transport preserves every unlocalized function. -/
@[simp] theorem horizontalLocalizationCongr_base {S C : Type u}
    [CommRing S] [CommRing C] [Algebra S C] {x y : C} (h : x = y) (z : C) :
    horizontalLocalizationCongr (S := S) h (algebraMap C _ z) = algebraMap C _ z := by
  subst y
  rw [horizontalLocalizationCongr_def]
  rfl

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hp : 2 * k < depth)
local notation "F" => ResidueField R
local notation "C" => Coordinate W (π ^ k) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ k) b3 b4 b6
local notation "e" => residuePolygonEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
local notation "E" => residueHorizontalDifferenceIso D k hk0 hk b3 b4 b6 h3 h4 h6 hp
local notation "N" => residueNodeIso D k hk0 hk b3 b4 b6 h3 h4 h6 hp

/-- The normalization of the retained open preserves every original tensor function. -/
theorem residueHorizontalDifferenceEquiv_restriction (z : F ⊗[R] C) :
    residueHorizontalDifferenceEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hp
      (PrincipalOpenTensor.restriction (R := R) F x z) = algebraMap _ _ (e z) := by
  simp only [residueHorizontalDifferenceEquiv, residueHorizontalEquiv,
    AlgEquiv.trans_apply, PrincipalOpenTensor.equiv_restriction]
  exact (congrArg (horizontalLocalizationCongr (S := F)
    (residuePolygonEquiv_x D k hk0 hk b3 b4 b6 h3 h4 h6 hp))
      (PrincipalOpenNormalization.equiv_base e
        (tensorX W (π ^ k) b3 b4 b6 F) z)).trans
          (horizontalLocalizationCongr_base _ _)

/-- The full horizontal normalization commutes with the original tensor inclusion. -/
@[reassoc] theorem residueHorizontalDifferenceIso_inclusion :
    (E).hom ≫ PrincipalOpenTensor.tensorInclusion (R := R) F x =
      PolygonNodeDifferenceBranches.inclusion (residueTangentUnit D)⁻¹ ≫ (N).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (residueHorizontalDifferenceEquiv_restriction
    D k hk0 hk b3 b4 b6 h3 h4 h6 hp)

/-- The retained negative puncture has exactly its original divided-chart inclusion. -/
@[reassoc] theorem residueHorizontalLeft_inclusion :
    residueHorizontalLeft D k hk0 hk b3 b4 b6 h3 h4 h6 hp ≫
      PrincipalOpenTensor.tensorInclusion (R := R) F x = PolygonNodeBranches.left F ≫ (N).hom := by
  rw [residueHorizontalLeft, Category.assoc, residueHorizontalDifferenceIso_inclusion,
    ← Category.assoc, PolygonNodeDifferenceBranches.left_inclusion]

/-- The retained positive puncture has exactly its original divided-chart inclusion. -/
@[reassoc] theorem residueHorizontalRight_inclusion :
    residueHorizontalRight D k hk0 hk b3 b4 b6 h3 h4 h6 hp ≫
      PrincipalOpenTensor.tensorInclusion (R := R) F x = PolygonNodeBranches.right F ≫ (N).hom := by
  rw [residueHorizontalRight, Category.assoc, residueHorizontalDifferenceIso_inclusion,
    ← Category.assoc, PolygonNodeDifferenceBranches.right_inclusion]

end FLT.Mazur.WeierstrassDilatation
