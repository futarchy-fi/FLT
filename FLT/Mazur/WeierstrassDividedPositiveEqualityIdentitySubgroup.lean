/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityOriginalSmooth
public import FLT.Mazur.PolygonSplitIdentityGroup
import all FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothGroup

/-!
# The original smooth group is the actual connected identity subgroup

The full cubic group law, reciprocal cyclic orientation and original
contraction agree. Every subgroup morphism retains its original geometric map.
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
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "G" => PolygonSplitGroup.model K (2 * s + 4)
local notation "M" => positiveEqualityCycleSmoothMap hπ data D s hs hstart hk hp

/-- The original smooth cubic group maps into the split smooth group with the actual orientation. -/
def positiveEqualityOriginalSmoothGroupHom : integralSmoothGroup V ⟶ CommGrp.mk G :=
  (infinityResidueSmoothGroupIso D hd).hom ≫
    PolygonSplitGroup.reciprocalIdentityGroupHom K (2 * s + 4)

/-- The subgroup inclusion is exactly the original smooth embedding in the whole actual fiber. -/
@[reassoc] theorem positiveEqualityOriginalSmoothGroupHom_inclusion :
    (positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom.left ≫ (M).left =
      positiveEqualityOriginalSmoothMap hπ data D s hs hk := by
  change ((infinityResidueSmoothGroupIso D hd).hom.hom.hom.hom.left ≫
    (PolygonSplitGroup.reciprocalIdentityGroupHom K (2 * s + 4)).hom.hom.hom.left) ≫
      (M).left = _
  rw [infinityResidueSmoothGroupIso_hom, PolygonSplitGroup.reciprocalIdentityGroupHom_left]
  simp only [Category.assoc]
  change (infinityResidueSmoothIso D hd).inv ≫ (ProjectiveLine.inversion K).hom ≫
    (PolygonSplitGroup.component K (2 * s + 4) 0 ≫ M).left = _
  rw [positiveEqualityCycleSmoothMap_originalSmooth, Iso.inv_hom_id_assoc]

include hπ data hs hstart hp in
/-- The underlying original group inclusion is a monomorphism of schemes. -/
theorem positiveEqualityOriginalSmoothGroupHom_mono :
    Mono (positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom.left := by
  have hm : Mono ((positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom.left ≫
      (M).left) := by
    rw [positiveEqualityOriginalSmoothGroupHom_inclusion hπ data D s hs hstart hk hp]
    infer_instance
  exact mono_of_mono (positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom.left
    (M).left

/-- Every group-scheme map, including finite subgroup inclusions, keeps its original geometry. -/
@[reassoc] theorem positiveEqualityOriginalSubgroup_inclusion
    {H : CommGrp (Over (Spec (.of K)))} (i : H ⟶ integralSmoothGroup V) :
    (i ≫ positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom.left ≫ (M).left =
      i.hom.hom.hom.left ≫ positiveEqualityOriginalSmoothMap hπ data D s hs hk := by
  change (i.hom.hom.hom.left ≫
    (positiveEqualityOriginalSmoothGroupHom D s hk).hom.hom.hom.left) ≫ (M).left = _
  rw [Category.assoc, positiveEqualityOriginalSmoothGroupHom_inclusion]

include hπ data hs hstart hp in
/-- The original smooth inclusion loses no group-scheme maps from any test group. -/
theorem positiveEqualityOriginalSubgroup_injective
    (H : CommGrp (Over (Spec (.of K)))) :
    Function.Injective (fun i : H ⟶ integralSmoothGroup V =>
      i ≫ positiveEqualityOriginalSmoothGroupHom D s hk) := by
  intro i j hij
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono (positiveEqualityOriginalSmoothMap hπ data D s hs hk)).mp
  have he := congrArg (fun a => a.hom.hom.hom.left ≫ (M).left) hij
  simpa only [positiveEqualityOriginalSubgroup_inclusion] using he

end FLT.Mazur.WeierstrassDividedDepth
