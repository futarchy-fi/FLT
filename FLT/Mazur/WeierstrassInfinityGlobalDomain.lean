/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityChartSpecialization
public import FLT.Mazur.WeierstrassGlobalInfinitySwap

/-!
# The genuine infinity law inside the global curve product

The original two-stage infinity neighborhood is an open of the true product.
Its two global projections are its actual Y-chart inputs, and global addition
restricts to its normalized dz/dx formula.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original infinity addition domain as an open of the global product. -/
def infinityGlobalDomain : Spec (.of (InfinityAdditionOpen W)) ⟶ integralCurveProduct W :=
  infinityAdditionInclusion W ≫ integralCurveProductChart W true true

instance infinityGlobalDomain_isOpenImmersion : IsOpenImmersion (infinityGlobalDomain W) := by
  unfold infinityGlobalDomain
  infer_instance

/-- The first global projection is precisely the original Y-chart input. -/
@[reassoc] theorem infinityGlobalDomain_fst :
    infinityGlobalDomain W ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) ≫
        integralCurveChart W 1 := by
  rw [infinityGlobalDomain, Category.assoc, integralCurveProductChart_fst]
  change infinityAdditionInclusion W ≫
    Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom) ≫ _ = _
  rw [← Category.assoc, infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The second global projection is precisely the original Y-chart input. -/
@[reassoc] theorem infinityGlobalDomain_snd :
    infinityGlobalDomain W ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) ≫
        integralCurveChart W 1 := by
  rw [infinityGlobalDomain, Category.assoc, integralCurveProductChart_snd]
  change infinityAdditionInclusion W ≫
    Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) ≫ _ = _
  rw [← Category.assoc, infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The global law restricts to the original normalized infinity output. -/
@[reassoc] theorem infinityGlobalDomain_addition (hΔ : IsUnit W.Δ) :
    infinityGlobalDomain W ≫ integralCurveAddition W hΔ =
      infinityAdditionSpec W ≫ integralCurveChart W 1 :=
  (Category.assoc _ _ _).trans (integralCurveAddition_infinity W hΔ)

/-- The infinity input domain carries its original coefficient-ring structure. -/
@[reassoc] theorem infinityGlobalDomain_structure :
    infinityGlobalDomain W ≫ pullback.fst _ _ ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionOpen W))) := by
  rw [infinityGlobalDomain_fst_assoc, integralCurveChart_structure]
  exact specAlgHom_base R (infinityInputLeft W)

end FLT.Mazur.WeierstrassIntegralChart
