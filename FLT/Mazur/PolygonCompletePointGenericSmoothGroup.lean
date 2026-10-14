/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericCubicGroup

/-!
# The complete smooth cubic specializes to the original field group

The two independently chosen equations are compared by their actual pointed
Cartesian morphism. The complete equation can have a nodal closed fiber; its
smooth group still becomes exactly the original group on every generic field square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Compose inverse projection equations before instantiating a geometric group law. -/
theorem isoComp_inv_projection {S Z : Scheme} {G H J : CommGrp (Over S)}
    (e : G ≅ H) (d : H ≅ J) (f : G.X.left ⟶ Z) (g : H.X.left ⟶ Z)
    (h : J.X.left ⟶ Z) (he : e.inv.hom.hom.hom.left ≫ f = g)
    (hd : d.inv.hom.hom.hom.left ≫ g = h) :
    (e ≪≫ d).inv.hom.hom.hom.left ≫ f = h := by
  change (d.inv.hom.hom.hom.left ≫ e.inv.hom.hom.hom.left) ≫ f = h
  rw [Category.assoc, he, hd]

/-- Equality transport retains projection followed by any original scheme morphism. -/
theorem inverseCongrIso_fst_post {S T Z : Scheme} {f g : T ⟶ S}
    (h : f = g) (G : CommGrp (Over S)) (k : G.X.left ⟶ Z) :
    (congrIso h G).inv.hom.hom.hom.left ≫ pullback.fst G.X.hom f ≫ k =
      pullback.fst G.X.hom g ≫ k := by
  rw [← Category.assoc, inverseCongrIso_fst]

end FLT.Mazur.GroupSchemeBaseChange

namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a))) (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "b" => s ≫ Scheme.toSpecΓ (S₀)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "V" => completeCartesianPointWeierstrass K n h L s p q hs i
local notation "f" => completePointFieldCubicMap K n h L a ha p q hs i
local notation "E" => completeFieldCubicGroupIso K n h L a ha p q hs i

/-- The generic smooth cubic group is the original independently constructed field group. -/
irreducible_def completePointGenericSmoothGroupIso :
    (Over.pullback b).mapCommGrp.obj (integralSmoothGroup W) ≅
      completeFieldGroup K n h L a ha p q hs i :=
  GroupSchemeBaseChange.congrIso (Spec.map_preimage b).symm (integralSmoothGroup W) ≪≫
    completePointFieldSmoothCubicGroupIso K n h L a ha p q hs i ≪≫ (E).symm

/-- Its inverse projects to the unchanged complete contraction on the original field square. -/
@[reassoc] theorem completePointGenericSmoothGroupIso_inv_fst :
    (completePointGenericSmoothGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W) b ≫ (integralSmoothOpen W).ι =
        p ≫ completePointToIntegralCubic K n h i := by
  rw [completePointGenericSmoothGroupIso_def]
  apply GroupSchemeBaseChange.isoComp_inv_projection
    (GroupSchemeBaseChange.congrIso (Spec.map_preimage b).symm (integralSmoothGroup W))
    (completePointFieldSmoothCubicGroupIso K n h L a ha p q hs i ≪≫ (E).symm)
    _ (pullback.fst (integralSmoothStructure W) (Spec.map (Spec.preimage b)) ≫
      (integralSmoothOpen W).ι) _
  · exact GroupSchemeBaseChange.inverseCongrIso_fst_post
      (Spec.map_preimage b).symm (integralSmoothGroup W) (integralSmoothOpen W).ι
  · apply GroupSchemeBaseChange.isoComp_inv_projection
      (completePointFieldSmoothCubicGroupIso K n h L a ha p q hs i) (E).symm _ f _
    · exact completePointFieldSmoothCubicGroupIso_inv_fst K n h L a ha p q hs i
    · change (E).hom.hom.hom.hom.left ≫ f = _
      rw [completeFieldCubicGroupIso_hom, completePointFieldCubicMap, Iso.hom_inv_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
