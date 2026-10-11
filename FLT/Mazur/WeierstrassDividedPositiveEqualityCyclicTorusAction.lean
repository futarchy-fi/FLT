/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityActionComparison
public import FLT.Mazur.PolygonSplitIdentityGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# The reciprocal cyclic torus as the original smooth group

The cyclic torus parameter is inverted before entering the original cubic.
With this orientation, the two actions agree on all points of component zero.
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


/-- The cyclic Laurent parameter identifies the actual original smooth group reciprocally. -/
def positiveEqualityCyclicSmoothGroupIso :
    CommGrp.mk (MultiplicativeGroupScheme.gm K) ≅ integralSmoothGroup V :=
  (PolygonSplitGroup.reciprocalGroupIso K).symm ≪≫ (infinityResidueSmoothGroupIso D hd).symm

omit [IsBezout R] in
/-- The reciprocal identification followed by the original inclusion is exactly component zero. -/
@[reassoc] theorem positiveEqualityCyclicSmoothGroupIso_inclusion :
    (positiveEqualityCyclicSmoothGroupIso D s hk).hom.hom.hom.hom ≫
        (positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom =
      PolygonSplitGroup.component K (2 * s + 4) 0 := by
  have h : (positiveEqualityCyclicSmoothGroupIso D s hk).hom ≫
      positiveEqualityOriginalSmoothGroupHom D s hk =
      PolygonSplitGroup.identityComponentGroupHom K (2 * s + 4) := by
    simp only [positiveEqualityCyclicSmoothGroupIso, Iso.trans_hom, Iso.symm_hom,
      positiveEqualityOriginalSmoothGroupHom, PolygonSplitGroup.reciprocalIdentityGroupHom,
      Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.hom.hom.hom) h

variable (T : Over (Spec (CommRingCat.of (ResidueField R))))
local notation "c" => PolygonSplitGroup.component K (2 * s + 4) 0
local notation "J" => positiveEqualityOriginalSmoothGroupHom D s hk
local notation "A" => positiveEqualityCycleAction hπ data D s hs hstart hk hp

/-- The cyclic torus point is the original smooth point with the proved reciprocal coordinate. -/
theorem positiveEqualityCyclicSmoothPoint_inclusion
    (b : T ⟶ MultiplicativeGroupScheme.gm K) :
    finiteGlobalSmoothCoefficientOverPoint hπ data (s + 1) hs K T
        (b ≫ (positiveEqualityCyclicSmoothGroupIso D s hk).hom.hom.hom.hom) =
      b ≫ c ≫ M := by
  rw [← positiveEqualityOriginalSmoothPoint_inclusion hπ data D s hs hstart hk hp,
    Category.assoc, positiveEqualityCyclicSmoothGroupIso_inclusion_assoc]

/-- The actual integral specialization agrees with the polygon action on the cyclic zero torus. -/
theorem positiveEqualityCycleAction_zeroTorusPoint
    (a : T ⟶ (integralSmoothGroup V).X) (b : T ⟶ MultiplicativeGroupScheme.gm K) :
    lift (a ≫ (J).hom.hom.hom) (b ≫ c ≫ M) ≫ A = a • (b ≫ c ≫ M) := by
  rw [← positiveEqualityCyclicSmoothPoint_inclusion hπ data D s hs hstart hk hp T b]
  exact positiveEqualityCycleAction_originalSmoothPoint hπ data D s hs hstart hk hp T a _

end FLT.Mazur.WeierstrassDividedDepth
