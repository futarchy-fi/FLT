/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericComparison
public import FLT.Mazur.WeierstrassCartesianSmoothPullbackGroup

/-!
# The complete smooth cubic specializes to the original field cubic group

The two independently chosen equations are compared by their actual pointed
Cartesian morphism. The complete equation can have a nodal closed fiber; its
smooth group still becomes exactly the original group on every generic field square.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange

/-- The inverse equality transport also retains the original fiber-product projection. -/
@[reassoc] theorem inverseCongrIso_fst {S T : Scheme} {f g : T ⟶ S}
    (h : f = g) (G : CommGrp (Over S)) :
    (congrIso h G).inv.hom.hom.hom.left ≫ pullback.fst G.X.hom f =
      pullback.fst G.X.hom g := by
  subst g
  exact Category.id_comp _

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

/-- The coefficient algebra is induced by the actual field-to-original-spectrum morphism. -/
abbrev completePointFieldCoefficientAlgebra : Algebra Γ(S₀, ⊤) L :=
  (Spec.preimage b).hom.toAlgebra

/-- The induced coefficient algebra retains exactly the original spectrum morphism. -/
theorem completePointFieldCoefficient_spec :
    let _ := completePointFieldCoefficientAlgebra K L a
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S₀, ⊤) L)) = b := Spec.map_preimage b

/-- The complete smooth group after the specified coefficient algebra is the field cubic group. -/
irreducible_def completePointFieldSmoothCubicGroupIso :
    (Over.pullback (Spec.map (Spec.preimage b))).mapCommGrp.obj (integralSmoothGroup W) ≅
      completeProjectiveGroup K n h L a ha p q hs i := by
  let _ := completePointFieldCoefficientAlgebra K L a
  have hf : IsPullback f (integralCurveStructure V) (integralCurveStructure W)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S₀, ⊤) L))) := by
    rw [completePointFieldCoefficient_spec]
    exact completePointFieldCubicMap_isPullback K n h L a ha p q hs i
  have hz : integralCurveZero V ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S₀, ⊤) L)) ≫ integralCurveZero W := by
    rw [completePointFieldCoefficient_spec]
    exact completePointFieldCubicMap_zero K n h L a ha p q hs i
  exact cartesianSmoothPullbackGroupIso W V f hf hz _

/-- The coefficient comparison retains the original whole-cubic map. -/
@[reassoc] theorem completePointFieldSmoothCubicGroupIso_inv_fst :
    (completePointFieldSmoothCubicGroupIso K n h L a ha p q hs i).inv.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W) (Spec.map (Spec.preimage b)) ≫
        (integralSmoothOpen W).ι = f := by
  let _ := completePointFieldCoefficientAlgebra K L a
  rw [completePointFieldSmoothCubicGroupIso_def]
  exact cartesianSmoothPullbackGroupIso_inv_fst W V f _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
