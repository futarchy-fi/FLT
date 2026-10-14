/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericCubicIso
public import FLT.Mazur.PolygonCompleteSmoothFieldCoefficientGroup

/-!
# The original field cubic maps to the complete cubic by a pointed Cartesian map

Both cubic comparisons retain the same original family and marking. Their
composite therefore supplies the actual pointed Cartesian map needed to compare
the independently constructed field law with the complete smooth law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
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
local notation "W" => completePointWeierstrassCurve K n h i
local notation "V" => completeCartesianPointWeierstrass K n h L s p q hs i
local notation "e" => completeCartesianPointProjectiveIso K n h L a ha p q hs i
local notation "g" => completePointToIntegralCubic K n h i

/-- The actual complete contraction expressed in the independently constructed field cubic. -/
def completePointFieldCubicMap : integralCurve V ⟶ integralCurve W :=
  (e).inv ≫ p ≫ g

/-- The comparison preserves the original coefficient-spectrum morphism. -/
@[reassoc] theorem completePointFieldCubicMap_over :
    completePointFieldCubicMap K n h L a ha p q hs i ≫ integralCurveStructure W =
      integralCurveStructure V ≫ s ≫ (S₀).toSpecΓ := by
  change (e).inv ≫ p ≫ g ≫ _ = _
  rw [completePointToIntegralCubic_over, ← Category.assoc p, hs.w, Category.assoc]
  simp only [← completeCartesianPointProjectiveIso_over K n h L a ha p q hs i,
    Category.assoc, Iso.inv_hom_id_assoc]

include ha hs in
/-- The whole original field square is Cartesian over the original complete cubic. -/
theorem completePointGenericCubic_isPullback :
    IsPullback (p ≫ g) q (integralCurveStructure W) (s ≫ (S₀).toSpecΓ) := by
  have hc : (p ≫ g) ≫ integralCurveStructure W = q ≫ (s ≫ (S₀).toSpecΓ) := by
    rw [Category.assoc, completePointToIntegralCubic_over, ← Category.assoc p, hs.w,
      Category.assoc]
  exact IsPullback.of_iso_pullback ⟨hc⟩
    (completePointGenericCubicIso K n h L a ha p q hs i)
    (completePointGenericCubicIso_fst K n h L a ha p q hs i)
    (completePointToCubicBaseChange_snd K n h s p q hs i)

/-- The field-to-complete cubic comparison is Cartesian, without comparing equations by fiat. -/
theorem completePointFieldCubicMap_isPullback :
    IsPullback (completePointFieldCubicMap K n h L a ha p q hs i)
      (integralCurveStructure V) (integralCurveStructure W) (s ≫ (S₀).toSpecΓ) := by
  refine (completePointGenericCubic_isPullback K n h L a ha p q hs i).of_iso
    e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (p ≫ g) ≫ 𝟙 _ = (e).hom ≫ (e).inv ≫ p ≫ g
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (completeCartesianPointProjectiveIso_over K n h L a ha p q hs i).symm
  · simp
  · simp

/-- Both retained markings are the actual infinity sections of their respective cubics. -/
@[reassoc] theorem completePointFieldCubicMap_zero :
    integralCurveZero V ≫ completePointFieldCubicMap K n h L a ha p q hs i =
      (s ≫ (S₀).toSpecΓ) ≫ integralCurveZero W := by
  have he : completeCartesianMarking K n h s p q hs i ≫ (e).hom =
      integralCurveZero V := completeCartesianPointToProjective_marking K n h L a ha p q hs i
  rw [← he, Category.assoc]
  change _ ≫ (e).hom ≫ (e).inv ≫ p ≫ g = _
  rw [Iso.hom_inv_id_assoc, completeCartesianMarking_fst_assoc,
    completePointToIntegralCubic_marking, Category.assoc]

end FLT.Mazur.PolygonInfinitesimalStages
