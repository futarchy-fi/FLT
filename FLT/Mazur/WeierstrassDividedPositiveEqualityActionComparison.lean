/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityIdentitySubgroup
public import FLT.Mazur.WeierstrassDividedPositiveEqualityLaurentAction
public import FLT.Mazur.PolygonSplitIdentityGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# Agreement of the two actions on the original identity orbit

The integral action specialized to the residue field agrees with the polygon
scaling action on the original smooth cubic, with its reciprocal orientation.
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

local notation "J" => positiveEqualityOriginalSmoothGroupHom D s hk
local notation "A" => positiveEqualityCycleAction hπ data D s hs hstart hk hp
variable (T : Over (Spec (CommRingCat.of (ResidueField R))))

/-- The oriented group inclusion gives the actual retained smooth point of the finite model. -/
theorem positiveEqualityOriginalSmoothPoint_inclusion
    (a : T ⟶ (integralSmoothGroup V).X) :
    a ≫ (J).hom.hom.hom ≫ M = finiteGlobalSmoothCoefficientOverPoint hπ data (s + 1) hs K T a := by
  apply Over.OverMorphism.ext
  change a.left ≫ ((J).hom.hom.hom.left ≫ (M).left) =
    a.left ≫ finiteGlobalSmoothCoefficientEmbedding K hπ data (s + 1) hs
  rw [positiveEqualityOriginalSmoothGroupHom_inclusion,
    positiveEqualityOriginalSmoothMap_eq_coefficientEmbedding]

/-- On the original identity orbit the polygon action is the actual specialized action. -/
theorem positiveEqualityCycleAction_originalSmoothPoint
    (a b : T ⟶ (integralSmoothGroup V).X) :
    lift (a ≫ (J).hom.hom.hom)
        (finiteGlobalSmoothCoefficientOverPoint hπ data (s + 1) hs K T b) ≫ A =
      a • finiteGlobalSmoothCoefficientOverPoint hπ data (s + 1) hs K T b := by
  rw [finiteGlobalCoefficientOverPointAction_smooth,
    ← positiveEqualityOriginalSmoothPoint_inclusion hπ data D s hs hstart hk hp T b,
    ← positiveEqualityOriginalSmoothPoint_inclusion hπ data D s hs hstart hk hp T (a * b)]
  rw [← Category.assoc b (J).hom.hom.hom M,
    ← lift_whiskerLeft_assoc, positiveEqualityCycleAction_smooth_restriction]
  change ((a ≫ (J).hom.hom.hom) * (b ≫ (J).hom.hom.hom)) ≫ M = _
  rw [← MonObj.mul_comp, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
