/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericSmoothGroup
public import FLT.Mazur.PolygonCompletePointIdentityCubicGroup

/-!
# Generic specialization of the constructed original identity group

The complete-base identity group and the independently constructed original
field group agree through a proved group isomorphism. Its projection is the
actual lift of the original field square to the original identity open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Pulling back an inverse group comparison retains any specified projection equation. -/
theorem pulledIso_inv_projection {S T Z : Scheme} (b : T ⟶ S)
    {G H : CommGrp (Over S)} (e : G ≅ H) (k : G.X.left ⟶ Z) (l : H.X.left ⟶ Z)
    (he : e.inv.hom.hom.hom.left ≫ k = l) :
    ((Over.pullback b).mapCommGrp.mapIso e).inv.hom.hom.hom.left ≫
      pullback.fst G.X.hom b ≫ k = pullback.fst H.X.hom b ≫ l := by
  change ((Over.pullback b).mapCommGrp.map e.inv).hom.hom.hom.left ≫ _ ≫ k = _
  rw [← Category.assoc, map_hom_fst b e.inv, Category.assoc, he]

end FLT.Mazur.GroupSchemeBaseChange

namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
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
local notation "G" => completePointIdentityGroup K n h i
local notation "E" => completePointIdentityCubicGroupIso K n h i
local notation "F" => completePointGenericSmoothGroupIso K n h L a ha p q hs i

/-- The constructed original identity group becomes the original full field group. -/
irreducible_def completePointGenericIdentityGroupIso :
    (Over.pullback b).mapCommGrp.obj (G) ≅ completeFieldGroup K n h L a ha p q hs i :=
  (Over.pullback b).mapCommGrp.mapIso E ≪≫ F

/-- The inverse group comparison projects to the actual original identity-open lift. -/
@[reassoc] theorem completePointGenericIdentityGroupIso_inv_fst :
    (completePointGenericIdentityGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left ≫
      pullback.fst (G).X.hom b = completePointFieldToIdentity K n h i L a ha p q hs := by
  apply (cancel_mono (completePointSmoothCubicIso K n h i).hom).mp
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc]
  rw [completePointFieldToIdentity_cubic]
  rw [completePointGenericIdentityGroupIso_def]
  apply GroupSchemeBaseChange.isoComp_inv_projection
    ((Over.pullback b).mapCommGrp.mapIso E) F _
    (pullback.fst (integralSmoothStructure W) b ≫ (integralSmoothOpen W).ι) _
  · apply GroupSchemeBaseChange.pulledIso_inv_projection b E
    rw [completePointIdentityCubicGroupIso_inv, Iso.inv_hom_id_assoc]
  · exact completePointGenericSmoothGroupIso_inv_fst K n h L a ha p q hs i

/-- In the original whole polygon, its projection is precisely the supplied field square. -/
@[reassoc] theorem completePointGenericIdentityGroupIso_inv_original :
    (completePointGenericIdentityGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left ≫
      pullback.fst (G).X.hom b ≫ (completePointIdentityOpen K n h i).ι = p := by
  rw [completePointGenericIdentityGroupIso_inv_fst_assoc,
    completePointFieldToIdentity_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
