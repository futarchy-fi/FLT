/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericIdentityGroup
public import FLT.Mazur.GroupSchemeBaseIsoTransport

/-!
# The identity group over the original base has the original generic field group

Reindexing along the specified coefficient-spectrum isomorphism and actual
pullback composition identify the literal original-base group with the existing
field group. The inverse retains the original family projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupSchemeBaseChange
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
local notation "e" => asIso (Scheme.toSpecΓ (S₀))
local notation "G" => completePointIdentityGroup K n h i
local notation "H" => completePointOriginalBaseGroup K n h i
local notation "E" => baseIsoGroupComparison (e) (G)
local notation "F" => completePointGenericIdentityGroupIso K n h L a ha p q hs i

/-- The original-base identity group has the independently constructed original field group. -/
irreducible_def completePointOriginalGenericGroupIso :
    (Over.pullback s).mapCommGrp.obj (H) ≅ completeFieldGroup K n h L a ha p q hs i :=
  (Over.pullback s).mapCommGrp.mapIso (E) ≪≫
    (compIso s (e).hom (G)).symm ≪≫ F

/-- The inverse group comparison projects to the unchanged original identity-open lift. -/
@[reassoc] theorem completePointOriginalGenericGroupIso_inv_fst :
    (completePointOriginalGenericGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left ≫
      pullback.fst (H).X.hom s = completePointFieldToIdentity K n h i L a ha p q hs := by
  rw [completePointOriginalGenericGroupIso_def]
  apply isoComp_inv_projection ((Over.pullback s).mapCommGrp.mapIso E)
    ((compIso s (e).hom (G)).symm ≪≫ F) _
    (pullback.fst ((Over.pullback (e).hom).obj (G).X).hom s ≫
      pullback.fst (G).X.hom (e).hom) _
  · have he := pulledIso_inv_projection s E (𝟙 _) (pullback.fst (G).X.hom (e).hom)
      (by simpa only [Category.comp_id] using baseIsoGroupComparison_inv (e) (G))
    simp only [Category.comp_id] at he
    exact he
  · apply isoComp_inv_projection (compIso s (e).hom (G)).symm F _
      (pullback.fst (G).X.hom (s ≫ (e).hom)) _
    · exact compIso_hom_fst_fst s (e).hom (G)
    · exact completePointGenericIdentityGroupIso_inv_fst K n h L a ha p q hs i

/-- On the original whole curve, the comparison is the original Cartesian projection. -/
@[reassoc] theorem completePointOriginalGenericGroupIso_inv_original :
    (completePointOriginalGenericGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left ≫
      pullback.fst (H).X.hom s ≫ (completePointIdentityOpen K n h i).ι = p := by
  rw [completePointOriginalGenericGroupIso_inv_fst_assoc,
    completePointFieldToIdentity_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
