/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityIdentitySubgroup
public import FLT.Mazur.WeierstrassSmoothProjectiveGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# Original field-valued points in the complete smooth identity subgroup

Every extension-field point retains its actual scheme map and original
addition law. The inclusion is injective and preserves all integer multiples.
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
open WeierstrassIntegralChart
local notation "k₀" => ResidueField R
local notation "V" => W.map (algebraMap R k₀)
local notation "G" => PolygonSplitGroup.model k₀ (2 * s + 4)
local notation "g" => Mon.Hom.hom (InducedCategory.Hom.hom
  (InducedCategory.Hom.hom (positiveEqualityOriginalSmoothGroupHom D s hk)))
local notation "M" => positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp
variable (L : Type u) [Field L] [Algebra (ResidueField R) L]
local notation "S" => Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k₀ L)))

/-- Postcomposition with the actual identity inclusion preserves the full point group law. -/
def positiveEqualitySmoothPointsHom : ((S) ⟶ (integralSmoothGroup V).X) →* ((S) ⟶ G) where
  toFun P := P ≫ g
  map_one' := MonObj.one_comp g
  map_mul' P Q := MonObj.mul_comp P Q g

/-- Every original nonsingular projective point maps with its original addition law. -/
def positiveEqualityOriginalPointHom :
    ((V).map (algebraMap k₀ L)).toProjective.Point →+ Additive ((S) ⟶ G) :=
  (positiveEqualitySmoothPointsHom D s hk L).toAdditive.comp
    (smoothProjectivePointAddEquiv (K := L) V).toAddMonoidHom

/-- The point inclusion retains its original morphism into the full residue cubic. -/
@[reassoc] theorem positiveEqualityOriginalPointHom_inclusion
    (P : ((V).map (algebraMap k₀ L)).toProjective.Point) :
    ((positiveEqualityOriginalPointHom D s hk L P).toMul ≫ M).left =
      projectiveToSmooth V P ≫ positiveEqualityOriginalSmoothMap hπ data D s hs hk := by
  change (projectiveToSmooth V P ≫ (g).left) ≫ (M).left = _
  rw [Category.assoc, positiveEqualityOriginalSmoothGroupHom_inclusion]

include hπ data hs hstart hp in
/-- Distinct original points remain distinct in the actual smooth group over every field. -/
theorem positiveEqualityOriginalPointHom_injective :
    Function.Injective (positiveEqualityOriginalPointHom D s hk L) := by
  let _ := positiveEqualityOriginalSmoothGroupHom_mono hπ data D s hs hstart hk hp
  intro P Q hPQ
  apply projectiveToSmoothOver_injective V
  apply Over.OverMorphism.ext
  apply (cancel_mono (g).left).mp
  exact congrArg (fun a => a.toMul.left) hPQ

include hπ data hs hstart hp in
/-- Integer torsion vanishes in the new group exactly when it vanishes originally. -/
theorem positiveEqualityOriginalPointHom_torsion_iff (m : ℤ)
    (P : ((V).map (algebraMap k₀ L)).toProjective.Point) :
    m • positiveEqualityOriginalPointHom D s hk L P = 0 ↔ m • P = 0 := by
  rw [← map_zsmul, ← map_zero (positiveEqualityOriginalPointHom D s hk L)]
  exact (positiveEqualityOriginalPointHom_injective hπ data D s hs hstart hk hp L).eq_iff

/-- Every original point subgroup is identified with its actual image, preserving its law. -/
def positiveEqualityOriginalPointSubgroupEquiv
    (H : AddSubgroup ((V).map (algebraMap k₀ L)).toProjective.Point) :
    H ≃+ H.map (positiveEqualityOriginalPointHom D s hk L) :=
  H.equivMapOfInjective (positiveEqualityOriginalPointHom D s hk L)
    (positiveEqualityOriginalPointHom_injective hπ data D s hs hstart hk hp L)

include hπ data hs hstart hp in
/-- In particular every finite original subgroup retains its exact order in the new fiber. -/
theorem positiveEqualityOriginalPointSubgroup_card
    (H : AddSubgroup ((V).map (algebraMap k₀ L)).toProjective.Point) :
    Nat.card (H.map (positiveEqualityOriginalPointHom D s hk L)) = Nat.card H :=
  Nat.card_congr (positiveEqualityOriginalPointSubgroupEquiv
    hπ data D s hs hstart hk hp L H).toEquiv.symm

end FLT.Mazur.WeierstrassDividedDepth
